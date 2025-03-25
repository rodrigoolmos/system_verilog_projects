`include "agent_spi_s.sv"
`include "agent_APB_m.sv"

module tb_apb_2_spi;

    timeunit 1ns;
    timeprecision 1ps;

    localparam integer t_clk         = 10;
    localparam integer BASE_ADDR     = 0;
    localparam integer FIFO_DEPTH    = 16;
    localparam integer CLK_FREC      = 100000000;   // Hz
    localparam integer SCL_FREC      = 1000000;     // Hz
    localparam integer NUM_TRANS_RX  = 256;

    localparam integer BYTE_SPI_TIME          = 8000; //ns
    localparam integer WAIT_BEFORE_SPI_TIME   = 1000; //ns
    localparam integer WAIT_AFTER_SPI_TIME    = 1000; //ns


    // @ddres periferal
    localparam ADDR_READ_TX_STATUS  = 4'b0000; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_WRITE_TX        = 4'b0000; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_READ_RX_STATUS  = 4'b0100; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_READ_RX_DATA    = 4'b1000; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_WRITE_N_READS   = 4'b1100; // word size 32 bits 4 bytes 2 bit @ddr

    // status periferal tx/rx
    localparam logic[3:0] FULL = 4'b1000;
    localparam logic[3:0] ALMOST_FULL = 4'b0100;
    localparam logic[3:0] EMPTY = 4'b0010;
    localparam logic[3:0] ALMOST_EMPTY = 4'b0001;

    // Instanciamos la clase APB (maestro)
    agent_APB_m agent_APB_m_h;
    // Instancia la clase SPI
    agent_spi#(NUM_TRANS_RX) agent_spi_h;

    logic send_receive;
    logic[31:0] apb_read_data;

    // spi if
    spi_if spi_if_inst();
    // apb if
    apb_if #(32, 32) apb_if_inst();

    task wait_transfer(int n_bytes);
        int i;
        for(i = 0; i < n_bytes; i++) begin
            #1;                     // wait load byte
            #BYTE_SPI_TIME;         // wait send byte
            #WAIT_AFTER_SPI_TIME;   // wait after send byte
        end
    endtask

    task send_recive_data(int n_bytes_send, int n_bytes_recive);
        int i;
        send_receive = 0;
        agent_APB_m_h.write_APB_data(n_bytes_recive, ADDR_WRITE_N_READS);
        for(i = 0; i < n_bytes_send; i++) begin
            agent_APB_m_h.write_APB_data(i, ADDR_WRITE_TX);
        end
        wait_transfer(n_bytes_send);
        send_receive = 1;
        for(i = 0; i < n_bytes_recive; i++) begin
            agent_spi_h.send_data(i);
        end
        #WAIT_AFTER_SPI_TIME;
        send_receive = 0;
        #1000;
        @(posedge apb_if_inst.pclk);
    endtask

    task send_data(int n_bytes_send);
        int i;
        send_receive = 0;
        agent_APB_m_h.write_APB_data(0, ADDR_WRITE_N_READS);
        for(i = 0; i < n_bytes_send; i++) begin
            agent_APB_m_h.write_APB_data(i, ADDR_WRITE_TX);
        end
        wait_transfer(n_bytes_send);
        #1000;
        @(posedge apb_if_inst.pclk);
    endtask

    task wait_fifo_tx_empty();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        while(apb_read_data != EMPTY) begin
            @(posedge apb_if_inst.pclk);
            agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        end
    endtask


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

    // Instanciamos el modulo APB a SPI
    apb_2_spi #(
        .BASE_ADDR(BASE_ADDR),
        .FIFO_DEPTH(FIFO_DEPTH),
        .CLK_FREC(CLK_FREC),
        .SCL_FREC(SCL_FREC)
    ) apb_2_spi_inst (
        .pclk(apb_if_inst.pclk),
        .presetn(apb_if_inst.presetn),
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
        .miso(spi_if_inst.miso),
        .mosi(spi_if_inst.mosi),
        .scl(spi_if_inst.scl),
        .cs(spi_if_inst.cs)
    );


    initial begin
        agent_spi_h = new(spi_if_inst, 0);
        agent_APB_m_h = new(apb_if_inst);
        send_receive = 0;

        @(posedge apb_if_inst.presetn);
        #10000 @(posedge apb_if_inst.pclk);

        send_data(16);
        wait_fifo_tx_empty();
        send_data(16);
        wait_fifo_tx_empty();
        send_data(3);
        wait_fifo_tx_empty();

        //wait(spi_if_inst.cs == 1'b1);
        #10000 @(posedge apb_if_inst.pclk);

        $stop;
    end

endmodule