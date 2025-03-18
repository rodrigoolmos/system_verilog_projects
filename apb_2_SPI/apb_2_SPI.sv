module apb_2_SPI #(
    parameter BASE_ADDR = 0,
    parameter FIFO_DEPTH = 16,
    parameter SCL_FREC = 9600,
    parameter CLK_FREC = 50000000
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
    input  logic [3:0]                pstrb,
    output logic                      pready,
    output logic [7:0]                prdata,
    output logic                      pslverr,

    // spi signals
    input  logic                      miso,
    output logic                      mosi,
    output logic                      scl,
    output logic                      cs
);

    logic       send_byte;
    logic       system_idle;
    logic       empty_tx;
    logic [7:0] byte_2_send;
    logic [7:0] receive_byte;
    logic       new_byte;

    apb_2_fifo #(
        .BASE_ADDR(BASE_ADDR),
        .DATA_WIDTH(8),
        .DEPTH(FIFO_DEPTH)
    )apb_2_fifo_inst
    (
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
        .read_fifo_tx(send_byte),
        .empty_tx(empty_tx),
        .almost_empty_tx(),             // not connected
        .fifo_r_data_tx(byte_2_send),

        // fifo out rx TODO
        .write_fifo_rx(new_byte),
        .full_rx(),                     // not connected
        .almost_full_rx(),              // not connected
        .fifo_w_data_rx(receive_byte)
    );

    always_comb send_byte = system_idle & ~empty_tx;

    spi_interface #(
        .CLK_FREC(CLK_FREC),
        .SCL_FREC(SCL_FREC)
    ) spi_inst (
        .clk(pclk),
        .arstn(presetn),
        .byte_send(byte_2_send),
        .byte_receive(),
        .send_byte(send_byte),
        .receive_byte(receive_byte),
        .system_idle(system_idle),
        .new_byte(new_byte),
        .miso(miso),
        .mosi(mosi),
        .scl(scl),
        .cs(cs)
    );

endmodule