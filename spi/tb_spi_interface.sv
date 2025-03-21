`include "agent_spi_s.sv"

module tb_spi_interface;

    timeunit 1ns;
    timeprecision 1ps;

    localparam N_ITERATIONS = 256;

    // Parámetros
    parameter CLK_FREC = 10000000;
    parameter SCL_FREC = 1000000;
    parameter NUM_TRANS_RX = 256;

    ////// Señales de testbench //////
    logic clk;
    logic arstn;
    // control signals
    logic[7:0]   byte_2_send;
    logic[7:0]   byte_received;
    logic        new_byte;
    logic        end_trans;
    logic        ena_spi;
    logic        msb_lsb;

    // Instancia la clase SPI
    agent_spi#(NUM_TRANS_RX) agent_spi_h;

    // uart if
    spi_if spi_if_inst();


    logic[7:0] data_sended[N_ITERATIONS-1:0];


    // Instancia del módulo SPI
    spi_interface #(
        .CLK_FREC(CLK_FREC),
        .SCL_FREC(SCL_FREC)
    ) spi_inst (
        .clk(clk),
        .arstn(arstn),
        .byte_2_send(byte_2_send),
        .byte_received(byte_received),
        .new_byte(new_byte),
        .end_trans(end_trans),
        .msb_lsb(msb_lsb),
        .ena_spi(ena_spi),
        .miso(spi_if_inst.miso),
        .mosi(spi_if_inst.mosi),
        .scl(spi_if_inst.scl),
        .cs(spi_if_inst.cs)
    );

    //checker
    spi_checker #(
        .CLK_FREC(CLK_FREC),
        .SCL_FREC(SCL_FREC)
    ) spi_checker_inst (
        .spi(spi_if_inst),
        .clk(clk),
        .arstn(arstn)
    );
    
    
    // Generación de reloj
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end 

    // Reset
    initial begin
        arstn = 0;
        #10 arstn = 1;
    end

    task send_byte_mosi(logic[7:0] byte_send);
        byte_2_send = byte_send;
        ena_spi = 1;
        agent_spi_h.recive_data();
        @(posedge end_trans);
        ena_spi = 0;
    endtask

    task continuous_transfer_mosi(int start_index, int end_index);

        ena_spi = 1;
        for (int i=start_index; i<end_index; ++i) begin
            byte_2_send = data_sended[i];
            agent_spi_h.recive_data();
            if (i== end_index - 1)
                @(posedge end_trans);
            else
                @(posedge new_byte);
        end
        ena_spi = 0;

    endtask

    task recive_byte_miso(logic[7:0] byte_receive);
        byte_2_send = 0;
        ena_spi = 1;
        agent_spi_h.send_data(byte_receive);
        @(posedge end_trans);
        ena_spi = 0;
        assert (byte_receive == byte_received)
            else $error("Assertion ERROR RECIVE MISO failed! %0d, %0d", byte_receive, byte_received);
    endtask

    task continuous_recive_miso(int start_index, int end_index);
        byte_2_send = 0;
        ena_spi = 1;
        for (int i=start_index; i<end_index; ++i) begin
            agent_spi_h.send_data(i);
            if (i== end_index - 1)
                @(posedge end_trans);
            else
                @(posedge new_byte);
            assert (i == byte_received)
                else $error("Assertion ERROR RECIVE MISO failed! %0d, %0d", i, byte_received);
        end
        ena_spi = 0;
    endtask

    function void generate_data(integer seed, logic mode);
        begin 
            for (int i=0; i<N_ITERATIONS; ++i) begin
                if (mode) begin
                    data_sended[i] = i+seed;
                end else begin
                    data_sended[i] = $urandom(i+seed);
                end
            end
        end
    endfunction 

    task test_msb_lsb(logic msb_lsb_param);
        $display("Test MSB_LSB %0d", msb_lsb_param);
        msb_lsb = msb_lsb_param;
        agent_spi_h.set_msb_lsb(msb_lsb_param);

        for (int i=0; i<56; ++i) begin
            send_byte_mosi(data_sended[i]);
            repeat(200) @(posedge clk);
        end

        for (int i=56; i<=206; i+=50) begin
            continuous_transfer_mosi(i, i + 50);
            repeat(200) @(posedge clk);
        end
        
        agent_spi_h.validate_received_bytes(data_sended);

        recive_byte_miso(8'h1);
        repeat(200) @(posedge clk);
        recive_byte_miso(8'h2);
        repeat(200) @(posedge clk);

        continuous_recive_miso(12, 51);
        repeat(200) @(posedge clk);
        continuous_recive_miso(34, 123);
        repeat(200) @(posedge clk);
        continuous_recive_miso(61, 191);
        repeat(200) @(posedge clk);
        recive_byte_miso(8'h1);
        repeat(200) @(posedge clk);
        
        agent_spi_h.reset_cnt_bytes();
    endtask

    initial begin
        $display("Test SPI Interface");
        generate_data(0, 1);
        msb_lsb = 0;
        // Inicialización de la clase SPI
        agent_spi_h = new(spi_if_inst, msb_lsb);

        // Inicialización de señales
        byte_2_send = 8'hFF;
        ena_spi = 0;
        
        @(posedge arstn);
        repeat(200) @(posedge clk);

        test_msb_lsb(0);
        test_msb_lsb(1);

        $display("End of test");
        $stop;
    end

endmodule