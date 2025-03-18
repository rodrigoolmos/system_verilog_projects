`include "agent_APB_m.sv"

module tb_apb_2_SPI;

    timeunit 1ns;
    timeprecision 1ps;

    const integer t_clk    = 10;
    parameter BASE_ADDR = 0;
    parameter FIFO_DEPTH = 16;
    parameter SCL_FREC = 9600;
    parameter CLK_FREC = 50000000;

    localparam ADDR_READ_TX_STATUS      = 4'b0000; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_WRITE_TX            = 4'b0000; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_READ_RX_STATUS      = 4'b0100; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_READ_RX_DATA        = 4'b1000; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_WRITE_BYTES_RECIVE  = 4'b1100; // word size 32 bits 4 bytes 2 bit @ddr

    localparam integer NUM_TRANS_RX = 32;
    localparam integer NUM_TRANS_TX = 64;


    // apb if
    apb_if #(32, 32) apb_if_inst();
    agent_APB_m agent_APB_m_h;

    // data for test
    // sended
    logic [7:0] data_miso_spi_send[NUM_TRANS_RX-1:0];
    logic [7:0] data_mosi_apb_send[NUM_TRANS_TX-1:0];
    
    // recived
    logic [7:0] data_rx_apb_recived[NUM_TRANS_RX-1:0];

    logic [31:0] data_apb_tmp;

    function void generate_data_mosi(integer seed, logic mode);
        begin 
            for (int i=0; i<NUM_TRANS_TX; ++i) begin
                if (mode) begin
                    data_mosi_apb_send[i] = i+seed;
                end else begin
                    data_mosi_apb_send[i] = $urandom(i+seed);
                end
            end
        end
    endfunction 

    function void generate_data_miso(integer seed, logic mode);
        begin 
            for (int i=0; i<NUM_TRANS_RX; ++i) begin
                if (mode) begin
                    data_miso_spi_send[i] = i+seed;
                end else begin
                    data_miso_spi_send[i] = $urandom(i+seed);
                end
            end
        end
    endfunction 

    apb_2_SPI #(
        .BASE_ADDR(BASE_ADDR),
        .FIFO_DEPTH(FIFO_DEPTH),
        .SCL_FREC(SCL_FREC),
        .CLK_FREC(CLK_FREC)
    )
    apb_2_SPI_ins(
        .pclk(apb_if_inst.pclk),
        .presetn(apb_if_inst.presetn),

        // apb
        .paddr(apb_if_inst.paddr),
        .pprot(apb_if_inst.pprot),
        .psel(apb_if_inst.psel),
        .penable(apb_if_inst.penable),
        .pwrite(apb_if_inst.pwrite),
        .pwdata(apb_if_inst.pwdata),
        .pstrb(apb_if_inst.pstrb),
        .pready(apb_if_inst.pready),
        .prdata(apb_if_inst.prdata),
        .pslverr(apb_if_inst.pslverr),

        // spi signals
        .miso(miso),
        .mosi(mosi),
        .scl(scl),
        .cs(cs)
    );

    // Generación del reloj para la interfaz APB
    initial begin
        apb_if_inst.pclk = 0;
        forever #(t_clk/2) apb_if_inst.pclk = ~apb_if_inst.pclk;
    end

    // Generación del reset
    initial begin
        apb_if_inst.presetn = 0;
        #100 @(posedge apb_if_inst.pclk);
        apb_if_inst.presetn = 1;
        @(posedge apb_if_inst.pclk);
    end

    initial begin
        generate_data_mosi(32, 1);
        generate_data_miso(71, 1);

        // Se instancia los agentes
        agent_APB_m_h = new(apb_if_inst);
    
        @(posedge apb_if_inst.presetn);
        repeat(10) @(posedge apb_if_inst.pclk);

        agent_APB_m_h.write_APB_data(8, ADDR_WRITE_BYTES_RECIVE);
        for (int i=0; i<16; ++i) begin
            agent_APB_m_h.write_APB_data(data_mosi_apb_send[i], ADDR_WRITE_TX);
        end

    end

endmodule