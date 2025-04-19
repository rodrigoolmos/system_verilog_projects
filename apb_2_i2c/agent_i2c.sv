`timescale 1ns/1ps

interface i2c_if;
    logic scl;
    wire sda;

    // Señal intermedia para controlar SDA desde el agente
    logic sda_slave_drive;

    // Asignación tri-state controlada por la señal intermedia
    assign sda = (sda_slave_drive === 1'b0) ? 1'b0 : 1'bz;

    modport master(output scl, inout sda);
    modport slave(input scl, inout sda, output sda_slave_drive);
endinterface

module i2c_checker(
    i2c_if              i2c_vif, 
    input  logic        clk,
    input  logic        arstn
);
    
    typedef enum logic[2:0] {idle, start, data, ack, stop} state_i2c_t;
    state_i2c_t state_i2c = idle;
    int n_starts = 0;
    int n_stops = 0;

    always_ff @(posedge clk or negedge arstn) begin
        if (!arstn) begin
            state_i2c <= idle;
        end else begin
            case (state_i2c)
                idle: begin
                    @(negedge i2c_vif.sda iff i2c_vif.scl);
                    n_starts++;
                    state_i2c <= start;
                end
                start: begin
                    if(i2c_vif.scl == 0)
                        state_i2c <= data;
                end
                data: begin
                    for (int i=0; i<8; ++i) begin
                        @(posedge i2c_vif.scl);
                    end
                    state_i2c <= ack;
                end
                ack: begin
                    @(posedge i2c_vif.scl);
                    state_i2c <= stop;
                end
                stop: begin
                    fork : stop_fork
                        begin
                            @(negedge i2c_vif.scl);
                            state_i2c <= data;
                        end
                        begin
                            @(posedge i2c_vif.sda iff i2c_vif.scl);
                            n_stops++;
                            state_i2c <= idle;
                        end
                    join_any
                    disable stop_fork;
                end
                default: begin
                    state_i2c <= idle;
                end
            endcase
        end
    end
    
    //START ASSERTION
    property p_start_only_in_idle;
        // En cada negedge de SDA con SCL alto…
        @(negedge i2c_vif.sda iff i2c_vif.scl) disable iff (!arstn)
        // …asegurase de que el estado sea idle
        state_i2c == idle;
    endproperty
    assert_start_idle: assert property (p_start_only_in_idle)
        else $error("Error: Start when not in idle state");

    //STOP ASSERTION
    property p_stop_only_in_data;
        // En cada posedge de SDA con SCL alto…
        @(posedge i2c_vif.sda iff i2c_vif.scl) disable iff (!arstn)
        // …asegurase de que el estado sea stop
        state_i2c == stop;
    endproperty
    assert_stop_data: assert property (p_stop_only_in_data)
        else $error("Error: Stop when not in stop state");

    //DATA ASSERTION
    property p_sda_stable_in_data;
        // En cada flanco de subida de clk...
        @(posedge clk) disable iff (!arstn)
        // si estamos en DATA y SCL=1…
        (state_i2c == data && i2c_vif.scl == 1) |-> 
            // …SDA debe ser stable
            $stable(i2c_vif.sda);
    endproperty
    assert_sda_stable_in_data: assert property (p_sda_stable_in_data)
        else $error("¡Error! SDA cambió mientras SCL=1 en estado DATA");


    // IDLE: si llegamos a idle, SDA y SCL deben estar ambos a ‘1’
    property p_bus_idle;
        @(posedge clk) disable iff (!arstn)
        // ANTECEDENTE: estamos en IDLE
        (state_i2c == idle)
            |-> 
        // CONSECUENTE: bus en reposo = SCL=1 & SDA=1
        (i2c_vif.scl == 1 && i2c_vif.sda == 1);
    endproperty
    assert_bus_idle: assert property (p_bus_idle)
        else $error("Error: bus no idle (SCL/SDA != 1) cuando state=IDLE");

endmodule

class agent_i2c #(parameter int N_RECEPTIONS = 256,
                    parameter logic[6:0] i2c_addr = 8'h00);

    virtual i2c_if.slave i2c_vif;

    logic [7:0] bytes_readed[N_RECEPTIONS-1:0];
    logic [7:0] bytes_expected[N_RECEPTIONS-1:0];
    integer write_pointer = 0;
    integer read_pointer = 0;
    logic [7:0] data;
    logic [7:0] addr_received;

    function new(virtual i2c_if.slave i2c_vif, logic [7:0] bytes_expected[N_RECEPTIONS-1:0]);
        this.i2c_vif = i2c_vif;
        for (int i=0; i<N_RECEPTIONS; ++i) begin
            this.bytes_readed[i] = 8'h00;
            this.bytes_expected[i] = bytes_expected[i];
        end
        this.i2c_vif.sda_slave_drive = 1'bz;
    endfunction

    task automatic read_byte_slave(ref logic [7:0] data);
        for (int i=0; i<8; ++i) begin
            @(posedge i2c_vif.scl);
            data[7-i] = i2c_vif.sda;
        end
        @(negedge i2c_vif.scl);
    endtask

    task automatic send_byte_slave(ref logic [7:0] data);
        #4000;
        wait(i2c_vif.scl == 0);
        for (int i=0; i<8; ++i) begin
            i2c_vif.sda_slave_drive = data[7-i] ? 1'bz : 1'b0;
            @(negedge i2c_vif.scl);
        end
        i2c_vif.sda_slave_drive = 1'bz; // libera al final
    endtask

    task gen_ack();
        #2000;
        i2c_vif.sda_slave_drive = 1'b0; // ACK=0
        @(posedge i2c_vif.scl);
        #6000;
        i2c_vif.sda_slave_drive = 1'bz; // libera tras ACK
    endtask

    task i2c_slave_handle_frame();
        @(negedge i2c_vif.sda iff i2c_vif.scl); // Start condition
        $display("Start condition detected, reading address");
        read_byte_slave(addr_received); // lee dirección
        $display("  Address received = %h actual address %h", addr_received[7:1], i2c_addr);
        if(i2c_addr == addr_received[7:1]) begin
            gen_ack();
            if(addr_received[0] == 1'b0)
                $display("  Write operation");
            else
                $display("  Read operation");
            fork : frame_fork
                begin
                    forever begin
                        if (addr_received[0] == 1'b0) begin
                            i2c_vif.sda_slave_drive = 1'bz;
                            read_byte_slave(data);
                            bytes_readed[read_pointer] = data;
                            expected_data : assert (bytes_readed[read_pointer] == bytes_expected[read_pointer])
                                else $error("Error los datos enviados y leidos no cuadran %h, %h", 
                                        bytes_readed[read_pointer], bytes_expected[read_pointer]);

                            $display("  Data readed = %h expected = %h", data, bytes_expected[read_pointer]);
                            read_pointer++;
                        end else if (addr_received[0] == 1'b1) begin
                            data = bytes_readed[write_pointer];
                            send_byte_slave(data);
                            write_pointer++;
                            $display("  Data sended = %h", data);
                        end
                        gen_ack();
                        $display("  ACK sent");
                        //@(negedge i2c_vif.scl);
                    end
                end

                begin
                    @(posedge i2c_vif.sda iff i2c_vif.scl); // stop condition
                    $display("  End of transmission");
                end 
            join_any
	    disable frame_fork;
        end

        i2c_vif.sda_slave_drive = 1'bz; // asegura liberar tras finalizar
    endtask
endclass
