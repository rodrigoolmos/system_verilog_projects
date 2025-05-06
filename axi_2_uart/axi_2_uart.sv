module axi_2_uart #(
    parameter BASE_ADDR = 0,
    parameter FIFO_DEPTH = 16,
    parameter baudrate = 9600,
    parameter clk_frec = 50000000
) (
    // AXI
    input   logic                               S_AXI_ACLK,     // Clock source.
    input   logic                               S_AXI_ARESETN,  // Global reset source, active low.
    input   logic [3 : 0]                       S_AXI_AWADDR,   // Write address
    input   logic [2 : 0]                       S_AXI_AWPROT,   // Not used
    input   logic                               S_AXI_AWVALID,  // Write address valid. Master generates this signal when Write Address and control signals are valid
    output  logic                               S_AXI_AWREADY,  // Write address ready. Slave generates this signal when it can accept Write Address and control signals
    input   logic [31 : 0]                      S_AXI_WDATA,    // Write data
    input   logic [3 : 0]                       S_AXI_WSTRB,    // Write strobes. 4-bit signal indicating which of the 4-bytes of Write Data. Slaves can choose assume all bytes are valid
    input   logic                               S_AXI_WVALID,   // Write valid. Master generates this signal when Write Data and control signals are valid
    output  logic                               S_AXI_WREADY,   // Write ready. Slave generates this signal when it can accept Write Data and control signals
    output  logic [1 : 0]                       S_AXI_BRESP,    // Write response. 2-bit signal indicating the status of the write transaction
    output  logic                               S_AXI_BVALID,   // Write response valid. Slave generates this signal when the write response on the bus is valid.
    input   logic                               S_AXI_BREADY,   // Write response ready. Master generates this signal when it accepts the write response
    input   logic [3 : 0]                       S_AXI_ARADDR,   // Read address
    input   logic [2 : 0]                       S_AXI_ARPROT,   // Not used
    input   logic                               S_AXI_ARVALID,  // Read address valid. Master generates this signal when Read Address and control signals are valid
    output  logic                               S_AXI_ARREADY,  // Read address ready. Slave generates this signal when it can accept Read Address and control signals
    output  logic [31 : 0]                      S_AXI_RDATA,    // Read data. Data bus for read data
    output  logic [1 : 0]                       S_AXI_RRESP,    // Read response. 2-bit signal indicating the status of the read transaction
    output  logic                               S_AXI_RVALID,   // Read valid. Slave generates this signal when it has read data to be accepted by the master
    input   logic                               S_AXI_RREADY,   // Read ready. Master generates this signal when it accepts the read data 
    
    // uart
    input  logic                                rx,
    output logic                                tx
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
        .clk(S_AXI_ACLK),
        .arstn(S_AXI_ARESETN),
        .rx(rx),
        .byte_tx(byte_2_send),
        .start_tx(send_byte),
        .done_tx(done_tx),
        .byte_rx(byte_recived),
        .tx(tx),
        .new_byte_rx(new_byte_rx)
    );


    axi_2_fifo #(
        .BASE_ADDR(BASE_ADDR),
        .AXI_DATA_WIDTH(8),
        .AXI_ADDR_WIDTH(32),
        .DEPTH(FIFO_DEPTH)
    )axi_2_fifo_inst
    (

        // axi
        .S_AXI_ACLK(S_AXI_ACLK),
        .S_AXI_ARESETN(S_AXI_ARESETN),
        .S_AXI_AWADDR(S_AXI_AWADDR),
        .S_AXI_AWPROT(S_AXI_AWPROT),
        .S_AXI_AWVALID(S_AXI_AWVALID),
        .S_AXI_AWREADY(S_AXI_AWREADY),
        .S_AXI_WDATA(S_AXI_WDATA),
        .S_AXI_WSTRB(S_AXI_WSTRB),
        .S_AXI_WVALID(S_AXI_WVALID),
        .S_AXI_WREADY(S_AXI_WREADY),
        .S_AXI_BRESP(S_AXI_BRESP),
        .S_AXI_BVALID(S_AXI_BVALID),
        .S_AXI_BREADY(S_AXI_BREADY),
        .S_AXI_ARADDR(S_AXI_ARADDR),
        .S_AXI_ARPROT(S_AXI_ARPROT),
        .S_AXI_ARVALID(S_AXI_ARVALID),
        .S_AXI_ARREADY(S_AXI_ARREADY),
        .S_AXI_RDATA(S_AXI_RDATA),
        .S_AXI_RRESP(S_AXI_RRESP),
        .S_AXI_RVALID(S_AXI_RVALID),
        .S_AXI_RREADY(S_AXI_RREADY),
    
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