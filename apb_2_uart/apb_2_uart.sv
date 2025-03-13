module apb_2_uart #(
    parameter BASE_ADDR = 0,
    parameter FIFO_DEPTH = 16,
    parameter baudrate = 9600,
    parameter clk_frec = 50000000
) (
    input logic         clk,
    input logic         arstn,

    // uart
    input logic         rx,
    output logic        tx,

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
    output logic                      pslverr
);

    logic[7:0] byte_2_send;
    logic[7:0] byte_recived;
    logic send_byte;
    logic done_tx;
    logic new_byte_rx;

    physical_uart  #(
        .baudrate(baudrate),
        .clk_frec(clk_frec)
    )physical_uart_inst
    (
        .clk(clk),
        .arstn(arstn),
        .rx(rx),
        .byte_tx(byte_2_send),
        .start_tx(send_byte),
        .done_tx(done_tx),
        .byte_rx(byte_recived),
        .tx(tx),
        .new_byte_rx(new_byte_rx)
    );


    apb_2_fifo #(
        .BASE_ADDR(BASE_ADDR),
        .DATA_WIDTH(8),
        .DEPTH(FIFO_DEPTH)
    )apb_2_fifo_inst
    (
        .pclk(clk),
        .presetn(arstn),

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
    
        // fifo out rx
        .write_fifo_rx(new_byte_rx),
        .full_rx(),                     // not connected
        .almost_full_rx(),              // not connected
        .fifo_w_data_rx(byte_recived)
    );


    always_comb send_byte = done_tx & ~empty_tx;
    
endmodule