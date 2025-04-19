module apb_2_i2c #(
    parameter MSB_LSB = 1,                  // 1: MSB first, 0: LSB first
    parameter BASE_ADDR = 8,            
    parameter FIFO_DEPTH = 256,             // power of 2
    parameter CLK_FREQ  = 100_000_000,      // 100 MHz
    parameter BITS_WAIT = 2,
    parameter I2C_FREQ  = 100_000           // 100 kHz
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
    inout  logic                      sda,
    output logic                      scl);

    logic [7:0]                 byte_2_send;
    logic [7:0]                 byte_received;
    logic                       ena_i2c;
    logic                       end_trans;
    logic                       end_trans_ff;
    logic                       addr_trans;
    logic [7:0]                 adrr_r_w;
    logic                       transaction_ok;

    logic                       read_fifo_tx;
    logic                       empty_tx;
    logic                       almost_empty_tx;

    logic                       write_fifo_rx;
    logic                       full_rx;
    logic                       end_rx;
    logic                       almost_full_rx;


    i2c #(
        .CLK_FREQ(CLK_FREQ),
        .BITS_WAIT(BITS_WAIT),
        .I2C_FREQ(I2C_FREQ)
    )i2c_ins(
        .clk(pclk),
        .arstn(presetn),
    
        // control signals
        .byte_2_send(byte_2_send),          // byte to send laches the byte when end_trans is 1
        .byte_received(byte_received),      // byte received ready when end_trans is 1
        .ena_i2c(ena_i2c),                  // enable i2c interface trsnasaction when this signal is 1 
        // end of transaction lower ena_i2c when end_trans 1 if you dont want to send more bytes
        // when this signal is 1 the byte_received is ready to be read or the byte_2_send is ready to be written
        .end_trans(end_trans),
        .addr_trans(addr_trans),
        .msb_lsb(MSB_LSB),                  // msb = 1 or lsb = 0
        .adrr_r_w(adrr_r_w),                // slave addres + (r/w) bit
        .transaction_ok(transaction_ok),    // 1 = transaction ok 0 = transaction error
    
        // i2c signals
        .sda(sda),
        .scl(scl));
    

    apb_2_fifo #(
        .BASE_ADDR(BASE_ADDR),
        .DATA_WIDTH(8),
        .DEPTH(FIFO_DEPTH)
    )apb_2_fifo_ins(
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
    
        // slave addres + (r/w) bit
        .adrr_r_w(adrr_r_w),
        .transaction_ok(transaction_ok),

        // fifo out tx
        .read_fifo_tx(read_fifo_tx),
        .empty_tx(empty_tx),
        .almost_empty_tx(almost_empty_tx),
        .fifo_r_data_tx(byte_2_send),
    
        // fifo in rx
        .write_fifo_rx(write_fifo_rx),
        .full_rx(full_rx),
        .end_rx(end_rx),
        .almost_full_rx(almost_full_rx),
        .fifo_w_data_rx(byte_received));

    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn)
            end_trans_ff <= 1'b0;
        else
            end_trans_ff <= end_trans;
    end

    always_comb begin
        ena_i2c = !end_rx || !empty_tx;
        read_fifo_tx = (end_trans && !end_trans_ff) && !addr_trans;
        write_fifo_rx = (end_trans && !end_trans_ff) && ! end_rx && !addr_trans;
    end

endmodule