// CPHA = 1
// CPOL = 1

module apb_2_spi #(
    parameter BASE_ADDR = 8,
    parameter FIFO_DEPTH = 256,    // power of 2
    parameter CLK_FREC = 100000000,
    parameter SCL_FREC = 1000000
) (
    input  logic                      pclk,
    input  logic                      presetn,

    // apb
    input  logic [31:0]               paddr,
    input  logic [2:0]                pprot,
    input  logic                      psel,
    input  logic                      penable,
    input  logic                      pwrite,
    input  logic [7:0]                pwdata,
    input  logic                      pstrb,
    output logic                      pready,
    output logic [7:0]                prdata,
    output logic                      pslverr,

    // spi signals
    input  logic                      miso,
    output logic                      mosi,
    output logic                      scl,
    output logic                      cs);
    
    logic [7:0] byte_2_send;
    logic empty_tx;
    logic read_fifo_tx;
    logic end_trans;
    logic ena_spi;

    spi_interface #(
        .CLK_FREC(CLK_FREC),
        .SCL_FREC(SCL_FREC)
    ) spi_inst (
        .clk(pclk),
        .arstn(presetn),
        
        // control signals
        .byte_2_send(byte_2_send),
        .byte_received(),               // TODO
        .new_byte(),                    // TODO
        .end_trans(end_trans),
        .msb_lsb(0),                    // 0: MSB first, 1: LSB first
        .ena_spi(ena_spi),
        
        // spi signals
        .miso(miso),
        .mosi(mosi),
        .scl(scl),
        .cs(cs)
    );

    always_comb read_fifo_tx = end_trans && !empty_tx;
    always_comb ena_spi = !empty_tx;


    apb_2_fifo #(
        .BASE_ADDR(BASE_ADDR),
        .DATA_WIDTH(8),
        .DEPTH(FIFO_DEPTH)
    ) apb_inst (
        .pclk(pclk),
        .presetn(presetn),

        // apb
        .paddr(paddr),
        .pprot(pprot),
        .psel(psel),
        .penable(penable),
        .pwrite(pwrite),
        .pwdata(pwdata),
        .pstrb(pstrb),
        .pready(pready),
        .prdata(prdata),
        .pslverr(pslverr),

        // fifo out tx
        .read_fifo_tx(read_fifo_tx),
        .empty_tx(empty_tx),            
        .almost_empty_tx(),             // not used
        .fifo_r_data_tx(byte_2_send),

        // fifo out rx
        .write_fifo_rx(),               // TODO
        .full_rx(),                     // not used
        .almost_full_rx(),              // not used
        .end_rx(end_rx),                     
        .fifo_w_data_rx()               // TODO    
    );

endmodule