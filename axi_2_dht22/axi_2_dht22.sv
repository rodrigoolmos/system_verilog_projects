module axi_2_dht22 #(
        parameter CLK_FREQ = 100000000
    )(
    input   logic                               S_AXI_ACLK,     // Clock source.
    input   logic                               S_AXI_ARESETN,  // Global reset source, active low.
    input   logic [1 : 0]                       S_AXI_AWADDR,   // Write address
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
    input   logic [1 : 0]                       S_AXI_ARADDR,   // Read address
    input   logic [2 : 0]                       S_AXI_ARPROT,   // Not used
    input   logic                               S_AXI_ARVALID,  // Read address valid. Master generates this signal when Read Address and control signals are valid
    output  logic                               S_AXI_ARREADY,  // Read address ready. Slave generates this signal when it can accept Read Address and control signals
    output  logic [31 : 0]                      S_AXI_RDATA,    // Read data. Data bus for read data
    output  logic [1 : 0]                       S_AXI_RRESP,    // Read response. 2-bit signal indicating the status of the read transaction
    output  logic                               S_AXI_RVALID,   // Read valid. Slave generates this signal when it has read data to be accepted by the master
    input   logic                               S_AXI_RREADY,   // Read ready. Master generates this signal when it accepts the read data 

    inout   logic                               dht22_in_out    // DHT22 data line
);
    
    localparam TRIGGER_TIME_S = 2;

    logic               data_ready;
    logic               sys_idle;
    logic[2:0][3:0]     humidity_bcd;
    logic               negativo_temp;
    logic [7:0]         parity;
    logic[2:0][3:0]     temperature_bcd;

    logic               start_read;
    logic[$clog2(CLK_FREQ*TRIGGER_TIME_S)-1:0] trigger_cnt;

    always_ff @(posedge S_AXI_ACLK) begin
        if (!S_AXI_ARESETN) begin
            trigger_cnt <= 0;
        end else begin
            if (trigger_cnt == CLK_FREQ*TRIGGER_TIME_S) begin
                trigger_cnt <= 0;
                start_read <= 1;
            end else begin
                trigger_cnt <= trigger_cnt + 1;
                start_read <= 0;
            end
        end
    end

    top_dht22 #(
            .CLK_FREQ(CLK_FREQ)
        )(
        .clk(S_AXI_ACLK),
        .arstn(S_AXI_ARESETN),
        .start_read(start_read),
        .dht22_in_out(dht22_in_out),
        .data_ready(data_ready),
        .sys_idle(sys_idle),
        .humidity_bcd(humidity_bcd),
        .negativo_temp(negativo_temp),
        .parity(parity),
        .temperature_bcd(temperature_bcd)
    );


    axi_lite_cntr #(
        .AXI_DATA_WIDTH(32),
        .AXI_ADDR_WIDTH(4)
    )axi_lite_cntr_inst(
        .S_AXI_ACLK(S_AXI_ACLK),        // Clock source.
        .S_AXI_ARESETN(S_AXI_ARESETN),  // Global reset source, active low.
        .S_AXI_AWADDR(S_AXI_AWADDR),    // Write address
        .S_AXI_AWPROT(S_AXI_AWPROT),    // Not used
        .S_AXI_AWVALID(S_AXI_AWVALID),  // Write address valid. Master generates this signal when Write Address and control signals are valid
        .S_AXI_AWREADY(S_AXI_AWREADY),  // Write address ready. Slave generates this signal when it can accept Write Address and control signals
        .S_AXI_WDATA(S_AXI_WDATA),      // Write data
        .S_AXI_WSTRB(S_AXI_WSTRB),      // Write strobes. 4-bit signal indicating which of the 4-bytes of Write Data. Slaves can choose assume all bytes are valid
        .S_AXI_WVALID(S_AXI_WVALID),    // Write valid. Master generates this signal when Write Data and control signals are valid
        .S_AXI_WREADY(S_AXI_WREADY),    // Write ready. Slave generates this signal when it can accept Write Data and control signals
        .S_AXI_BRESP(S_AXI_BRESP),      // Write response. 2-bit signal indicating the status of the write transaction
        .S_AXI_BVALID(S_AXI_BVALID),    // Write response valid. Slave generates this signal when the write response on the bus is valid.
        .S_AXI_BREADY(S_AXI_BREADY),    // Write response ready. Master generates this signal when it accepts the write response
        .S_AXI_ARADDR(S_AXI_ARADDR),    // Read address
        .S_AXI_ARPROT(S_AXI_ARPROT),    // Not used
        .S_AXI_ARVALID(S_AXI_ARVALID),  // Read address valid. Master generates this signal when Read Address and control signals are valid
        .S_AXI_ARREADY(S_AXI_ARREADY),  // Read address ready. Slave generates this signal when it can accept Read Address and control signals
        .S_AXI_RDATA(S_AXI_RDATA),      // Read data. Data bus for read data
        .S_AXI_RRESP(S_AXI_RRESP),      // Read response. 2-bit signal indicating the status of the read transaction
        .S_AXI_RVALID(S_AXI_RVALID),    // Read valid. Slave generates this signal when it has read data to be accepted by the master
        .S_AXI_RREADY(S_AXI_RREADY),    // Read ready. Master generates this signal when it accepts the read data    

        .bcd_humidity({negativo_temp, humidity_bcd}),
        .bcd_temperature({temperature_bcd}),
        .crc(parity),
        .status({data_ready, sys_idle})

    );


endmodule