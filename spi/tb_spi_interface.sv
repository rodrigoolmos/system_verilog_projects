module tb_spi_interface;

    timeunit 1ns;
    timeprecision 1ps;

    // Parámetros
    parameter CLK_FREC = 100000000;
    parameter SCL_FREC = 1000000;

    // Señales de testbench
    logic clk;
    logic arstn;
    logic[7:0] byte_send;
    logic[7:0] byte_receive;
    logic send_byte;
    logic receive_byte;
    logic system_idle;
    logic new_byte;

    logic miso;
    logic mosi;
    logic scl;
    logic cs;

    logic[7:0] slave_byte_recive;
    logic[7:0] slave_byte_expected;


    // Instancia del módulo SPI
    spi_interface #(
        .CLK_FREC(CLK_FREC),
        .SCL_FREC(SCL_FREC)
    ) spi_inst (
        .clk(clk),
        .arstn(arstn),
        .byte_send(byte_send),
        .byte_receive(byte_receive),
        .send_byte(send_byte),
        .receive_byte(receive_byte),
        .system_idle(system_idle),
        .new_byte(new_byte),
        .miso(miso),
        .mosi(mosi),
        .scl(scl),
        .cs(cs)
    );

    // monitor mosi
    initial begin
        int num_bit;
        fork
            begin
                forever begin
                    @(posedge scl iff ~cs);
                    slave_byte_recive[num_bit] = mosi;
                    num_bit++;
                end
            end
            begin
                forever begin
                    @(posedge send_byte);
                    num_bit = 0;
                    slave_byte_expected = byte_send;
                end
            end
            begin
                @(posedge arstn);
                forever begin
                    @(posedge system_idle);
                    assert (slave_byte_expected == slave_byte_recive)
                        else $error("ERROR byte enviado! %d, %d", slave_byte_expected, slave_byte_recive);
                end
            end
        join
    end

    // monitor cs
    initial begin
        @(posedge arstn);
        forever begin
            @(posedge clk);
            assert property (@(posedge clk) cs |-> ( $past(system_idle,1) && $past(system_idle,2)))
                else $error("Assertion ailed!");
        end
    end

    task master_send_byte(input logic[7:0] byte_to_send);

        byte_send = byte_to_send;
        send_byte = 1;
        @(posedge clk);
        send_byte = 0;
        @(posedge clk);
        wait(system_idle);

    endtask

    task master_recive_byte(input logic[7:0] byte_to_recive);

        receive_byte = 1;
        @(posedge clk);
        receive_byte = 0;
        @(posedge clk);
        for (int i=0; i<8; ++i) begin
            @(negedge scl);
            miso = byte_to_recive[i];
        end
	    @(posedge scl) @(posedge clk);
        miso = 0;
        wait(system_idle);

        assert (byte_receive == byte_to_recive)
            else $error("ERROR byte recivido! %d, %d", byte_receive, byte_to_recive);

    endtask

    task release_spi();
        wait(cs);
        repeat(30) @(posedge clk);
    endtask 

    // Generación de reloj
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // Genera un reloj de 100 MHz
    end 

    initial begin
        miso = 0;
        arstn = 0;
        byte_send = 0;
        send_byte = 0;
        receive_byte = 0;
        # 100ns;
        arstn = 1;
        @(posedge clk);
        
        master_send_byte(8'd1);
        master_send_byte(8'd2);
        master_send_byte(8'd3);
        master_send_byte(8'd4);
        master_recive_byte(8'd45);
        master_recive_byte(8'd53);
        master_recive_byte(8'd51);
        master_recive_byte(8'd25);

        release_spi();

        master_send_byte(8'd11);
        master_send_byte(8'd21);
        master_send_byte(8'd31);
        master_send_byte(8'd41);
        master_recive_byte(8'd43);
        master_recive_byte(8'd13);
        master_recive_byte(8'd53);
        master_recive_byte(8'd23);
        release_spi();


        #5us;
        $stop;
    end

endmodule