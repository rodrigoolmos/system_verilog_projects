`include "agent_spi_s.sv"

module tb_spi_interface;

    timeunit 1ns;
    timeprecision 1ps;

    // Parámetros
    parameter CLK_FREC = 100000000;
    parameter SCL_FREC = 1000000;
    parameter NUM_TRANS_RX = 256;

    ////// Señales de testbench //////
    logic clk;
    logic arstn;
    // control signals
    logic[7:0]   byte_2_send;
    logic[7:0]   byte_received;
    logic        new_byte;
    logic        ena_spi;
    // spi signals
    logic miso;
    logic mosi;
    logic scl;
    logic cs;

    // Instancia la clase SPI
    agent_spi#(NUM_TRANS_RX) agent_spi_h;

    // uart if
    spi_if spi_if_inst();


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
        .ena_spi(ena_spi),
        .miso(spi_if_inst.miso),
        .mosi(spi_if_inst.mosi),
        .scl(spi_if_inst.scl),
        .cs(spi_if_inst.cs)
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
        @(posedge new_byte);
        ena_spi = 0;
    endtask

    initial begin
        
        // Inicialización de la clase SPI
        agent_spi_h = new(spi_if_inst);

        // Inicialización de señales
        byte_2_send = 8'hFF;
        ena_spi = 0;
        

        @(posedge arstn);
        repeat(200) @(posedge clk);

        send_byte_mosi(8'h34);
        repeat(200) @(posedge clk);

        send_byte_mosi(8'h24);
        send_byte_mosi(8'h54);


        repeat(200) @(posedge clk);
        $stop;
    end

endmodule