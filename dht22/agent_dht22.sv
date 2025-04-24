`timescale 1ns/1ps

interface dht22_if;
    wire dht22_in_out;
    // Señal intermedia para controlar dht22_in_out desde el agente
    logic slave_drive;

    // Asignación tri-state controlada por la señal intermedia
    assign dht22_in_out = (slave_drive === 1'b0) ? 1'b0 : 1'bz;

    modport master(inout dht22_in_out);
    modport slave(inout dht22_in_out);


endinterface

module checker_dht22(
    dht22_if dht22_vif
);
    real t_rise, t_fall;
    real idle_start, idle_end;
    typedef enum logic[1:0] {start, data, idle} dht22_state_t;
    dht22_state_t dht22_state;

    initial begin
        dht22_state = idle;

        forever begin
            case (dht22_state)
                idle: begin
                    idle_start = $realtime;
                    @(negedge dht22_vif.dht22_in_out);
                    idle_end = $realtime;
                    $display("DHT22 idle time: %0.3f", idle_end - idle_start);
                    assert (idle_end - idle_start < 2000_000) else begin
                        $error("Error: DHT22 idle time is too short");
                    end
                    t_fall = $realtime;
                    dht22_state = start;
                end
                start: begin
                    @(posedge dht22_vif.dht22_in_out);
                    t_rise = $realtime;
                    dht22_state = data;
                    $display("DHT22 start time: %0.3f ns", t_fall - t_rise);
                    assert (t_fall - t_rise < 1000_000) else begin
                        $error("Error: DHT22 start signal is too short");
                    end
                end
                data: begin
                    for (int i=0; i<42; ++i) begin
                        @(negedge dht22_vif.dht22_in_out);
                        t_fall = $realtime;
                        @(posedge dht22_vif.dht22_in_out);
                        t_rise = $realtime;
                        if (t_rise - t_fall > 1000_000) begin
                            i = 0;
                        end
                    end
                    dht22_state = idle;
                end
            endcase
        end
    end

endmodule

class agent_dht22;

    virtual dht22_if dht22_vif;
    
    // Constructor que recibe el virtual interface
    function new(virtual dht22_if dht22_vif);
        this.dht22_vif = dht22_vif;
        this.dht22_vif.slave_drive = 1'bz;
    endfunction

    task send_bits(int unsigned n_bits, logic[15:0] bit_array);
        for (int i=n_bits-1; i>=0; i = i - 1) begin
            if (bit_array[i] == 0) begin
                dht22_vif.slave_drive = 1'b0;
                #50us;
                dht22_vif.slave_drive = 1'bz;
                #25us;
            end else begin
                dht22_vif.slave_drive = 1'b0;
                #50us;
                dht22_vif.slave_drive = 1'bz;
                #70us;
            end
        end
    endtask

    task automatic generate_dht22_data(const ref logic[15:0] data_humidity,
                                    const ref logic[15:0] data_temperature,
                                    const ref logic[7:0] data_parity);

        @(negedge dht22_vif.dht22_in_out);
        // host pull low
        @(posedge dht22_vif.dht22_in_out);
        #36us; // host pull UP

        dht22_vif.slave_drive = 1'b0;
        #80us;
        dht22_vif.slave_drive = 1'bz;
        #80us;

        // 16 bits RH data
        send_bits(16, data_humidity);

        // 16 bits T data
        send_bits(16, data_temperature);

        // 8 bits check sum
        send_bits(8, data_parity);

        dht22_vif.slave_drive = 1'b0;
        #50us;
        dht22_vif.slave_drive = 1'bz;

    endtask

    task automatic generate_dht22_error(const ref logic[15:0] data_humidity,
                                    const ref logic[15:0] data_temperature,
                                    const ref logic[7:0] data_parity);

        @(negedge dht22_vif.dht22_in_out);
        // host pull low
        @(posedge dht22_vif.dht22_in_out);
        #36us; // host pull UP

        dht22_vif.slave_drive = 1'b0;
        #80us;
        dht22_vif.slave_drive = 1'bz;
        #80us;

        // 16 bits RH data
        send_bits(16, data_temperature);

        // 16 bits T data missin

        // 8 bits check sum missin

        dht22_vif.slave_drive = 1'b0;
        #50us;
        dht22_vif.slave_drive = 1'bz;

    endtask

endclass