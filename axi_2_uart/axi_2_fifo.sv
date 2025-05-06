module axi_2_fifo #(
    parameter BASE_ADDR = 8,
    parameter AXI_DATA_WIDTH = 32,
    parameter AXI_ADDR_WIDTH = 32,
    parameter DEPTH = 16    // power of 2
) (
    // AXI
    input   logic                               S_AXI_ACLK,     // Clock source.
    input   logic                               S_AXI_ARESETN,  // Global reset source, active low.
    input   logic [AXI_ADDR_WIDTH-1 : 0]        S_AXI_AWADDR,   // Write address
    input   logic [2 : 0]                       S_AXI_AWPROT,   // Not used
    input   logic                               S_AXI_AWVALID,  // Write address valid. Master generates this signal when Write Address and control signals are valid
    output  logic                               S_AXI_AWREADY,  // Write address ready. Slave generates this signal when it can accept Write Address and control signals
    input   logic [AXI_DATA_WIDTH-1 : 0]        S_AXI_WDATA,    // Write data
    input   logic [(AXI_DATA_WIDTH/8)-1 : 0]    S_AXI_WSTRB,    // Write strobes. 4-bit signal indicating which of the 4-bytes of Write Data. Slaves can choose assume all bytes are valid
    input   logic                               S_AXI_WVALID,   // Write valid. Master generates this signal when Write Data and control signals are valid
    output  logic                               S_AXI_WREADY,   // Write ready. Slave generates this signal when it can accept Write Data and control signals
    output  logic [1 : 0]                       S_AXI_BRESP,    // Write response. 2-bit signal indicating the status of the write transaction
    output  logic                               S_AXI_BVALID,   // Write response valid. Slave generates this signal when the write response on the bus is valid.
    input   logic                               S_AXI_BREADY,   // Write response ready. Master generates this signal when it accepts the write response
    input   logic [AXI_ADDR_WIDTH-1 : 0]        S_AXI_ARADDR,   // Read address
    input   logic [2 : 0]                       S_AXI_ARPROT,   // Not used
    input   logic                               S_AXI_ARVALID,  // Read address valid. Master generates this signal when Read Address and control signals are valid
    output  logic                               S_AXI_ARREADY,  // Read address ready. Slave generates this signal when it can accept Read Address and control signals
    output  logic [AXI_DATA_WIDTH-1 : 0]        S_AXI_RDATA,    // Read data. Data bus for read data
    output  logic [1 : 0]                       S_AXI_RRESP,    // Read response. 2-bit signal indicating the status of the read transaction
    output  logic                               S_AXI_RVALID,   // Read valid. Slave generates this signal when it has read data to be accepted by the master
    input   logic                               S_AXI_RREADY,    


    // fifo out tx
    input  logic                                read_fifo_tx,
    output logic                                empty_tx,
    output logic                                almost_empty_tx,
    output logic [AXI_DATA_WIDTH-1:0]           fifo_r_data_tx,

    // fifo in rx
    input  logic                                write_fifo_rx,
    output logic                                full_rx,
    output logic                                almost_full_rx,
    input  logic [AXI_DATA_WIDTH-1:0]           fifo_w_data_rx
);

    localparam ADDR_READ_TX_STATUS  = 2'b00;
    localparam ADDR_WRITE_TX        = 2'b00;
    localparam ADDR_READ_RX_STATUS  = 2'b01;
    localparam ADDR_READ_RX_DATA    = 2'b10;

    localparam N_REGS_ADDR          = 3;



    logic[AXI_DATA_WIDTH-1:0]   regs_tx[DEPTH-1:0];
    logic[$clog2(DEPTH)-1:0]    index_write_tx;
    logic[$clog2(DEPTH)-1:0]    index_read_tx;
    logic[$clog2(DEPTH):0]      size_fifo_tx;
    logic                       almost_full_tx;
    logic                       full_tx;
    logic                       write_fifo_tx;


    logic[AXI_DATA_WIDTH-1:0]   regs_rx[DEPTH-1:0];
    logic[$clog2(DEPTH)-1:0]    index_write_rx;
    logic[$clog2(DEPTH)-1:0]    index_read_rx;
    logic[$clog2(DEPTH):0]      size_fifo_rx;
    logic                       almost_empty_rx;
    logic                       empty_rx;
    logic                       read_fifo_rx;

    /*******************      RX      *********************/
    // Logica escritura fifo rx
    always_ff @(posedge S_AXI_ACLK or negedge S_AXI_ARESETN) begin
        if (!S_AXI_ARESETN) begin
            index_write_rx <= 0;
            for (int i=0; i<DEPTH; ++i)
                regs_rx[i] <= 0;
        end else begin
            if (write_fifo_rx & ~full_rx) begin
                index_write_rx <= index_write_rx + 1;
                regs_rx[index_write_rx] <= fifo_w_data_rx;
            end
        end
    end

    // upodate index read fifo rx
    always_ff @(posedge S_AXI_ACLK or negedge S_AXI_ARESETN) begin
        if (!S_AXI_ARESETN) begin
            index_read_rx <= 0;
        end else begin
            if (read_fifo_rx & ~empty_rx) begin
                index_read_rx <= index_read_rx + 1;
            end
        end
    end

    // update size fifo rx
    always_ff @(posedge S_AXI_ACLK or negedge S_AXI_ARESETN) begin
        if (!S_AXI_ARESETN) begin
            size_fifo_rx <= DEPTH;
        end else begin
            case ({write_fifo_rx & ~full_rx, read_fifo_rx & ~empty_rx})
                2'b10: size_fifo_rx <= size_fifo_rx - 1;
                2'b01: size_fifo_rx <= size_fifo_rx + 1;
                default: size_fifo_rx <= size_fifo_rx;
            endcase        
        end
    end

    // calculate fifo size rx
    always_comb begin
        full_rx = size_fifo_rx == 0;
        almost_full_rx = size_fifo_rx == 1;
        empty_rx = size_fifo_rx == DEPTH;
        almost_empty_rx = size_fifo_rx == DEPTH - 1;
    end

    // enable read fifo rx
    always_comb read_fifo_rx = S_AXI_RVALID & S_AXI_RREADY & (S_AXI_ARADDR[3:2] == ADDR_READ_RX_DATA);

    /*******************      TX      *********************/
    // Logica escritura AXI a fifo tx
    always_ff @(posedge S_AXI_ACLK or negedge S_AXI_ARESETN) begin
        if (!S_AXI_ARESETN) begin
            index_write_tx <= 0;  
            for (int i=0; i<DEPTH; ++i)
                regs_tx[i] <= 0;
        end else if (write_fifo_tx & ~full_tx) begin
            index_write_tx <= index_write_tx + 1;
            regs_tx[index_write_tx] <= S_AXI_WDATA;
        end
    end

    // Logica lectura fifo tx
    always_ff @(posedge S_AXI_ACLK or negedge S_AXI_ARESETN) begin
        if (!S_AXI_ARESETN) begin
            index_read_tx <= 0;
        end else if (read_fifo_tx & ~empty_tx) begin
            index_read_tx <= index_read_tx + 1;
        end
    end

    // update size fifo tx
    always_ff @(posedge S_AXI_ACLK or negedge S_AXI_ARESETN) begin
        if (!S_AXI_ARESETN) begin
            size_fifo_tx <= DEPTH;
        end else begin
            case ({write_fifo_tx & ~full_tx, read_fifo_tx & ~empty_tx})
                2'b10: size_fifo_tx <= size_fifo_tx - 1;
                2'b01: size_fifo_tx <= size_fifo_tx + 1;
                default: size_fifo_tx <= size_fifo_tx;
            endcase        
        end
    end

    // calculate fifo size tx
    always_comb begin
        full_tx = size_fifo_tx == 0;
        almost_full_tx = size_fifo_tx == 1;
        empty_tx = size_fifo_tx == DEPTH;
        almost_empty_tx = size_fifo_tx == DEPTH - 1;
    end

    // read data from fifo tx
    always_comb fifo_r_data_tx = regs_tx[index_read_tx];

    /****************** AXI WRITE addr data handshake *****************/
    always_ff @(posedge S_AXI_ACLK or negedge S_AXI_ARESETN) begin
        if (!S_AXI_ARESETN) begin
            S_AXI_AWREADY <= 0;
            S_AXI_WREADY <= 0;
        end else begin
            if(S_AXI_WVALID && S_AXI_AWVALID && !S_AXI_AWREADY && !S_AXI_WREADY) begin
                S_AXI_AWREADY <= 1;
                S_AXI_WREADY <= 1;
            end else begin
                S_AXI_AWREADY <= 0;
                S_AXI_WREADY <= 0;
            end
        end  
    end

    // enable write to fifo tx
    always_comb write_fifo_tx = S_AXI_AWREADY & S_AXI_WREADY & (S_AXI_AWADDR[3:2] == ADDR_WRITE_TX);


    /****************** AXI READ addr data handshake *****************/
    always_ff @(posedge S_AXI_ACLK or negedge S_AXI_ARESETN) begin
        if (!S_AXI_ARESETN) begin
            S_AXI_ARREADY <= 0;
            S_AXI_RVALID <= 0;
        end else begin
            if(S_AXI_RREADY && S_AXI_ARVALID && !S_AXI_ARREADY && !S_AXI_RVALID ) begin
                S_AXI_ARREADY <= 1;
                S_AXI_RVALID <= 1;
            end else begin
                S_AXI_ARREADY <= 0;
                S_AXI_RVALID <= 0;
            end
        end  
    end

    // lectura AXI
    always_comb begin
        if (S_AXI_RVALID & S_AXI_RREADY) begin
            case (S_AXI_ARADDR[3:2])
                ADDR_READ_TX_STATUS: S_AXI_RDATA = {{28{1'b0}}, full_tx, almost_full_tx, empty_tx, almost_empty_tx};
                ADDR_READ_RX_STATUS: S_AXI_RDATA = {{28{1'b0}}, full_rx, almost_full_rx, empty_rx, almost_empty_rx};
                ADDR_READ_RX_DATA:   S_AXI_RDATA = regs_rx[index_read_rx];
                default: S_AXI_RDATA = 0;
            endcase
        end else begin
            S_AXI_RDATA = 0;
        end
    end

    always_ff @(posedge S_AXI_ACLK or negedge S_AXI_ARESETN) begin
        if (!S_AXI_ARESETN) begin
          S_AXI_BVALID <= 1'b0;
          S_AXI_BRESP  <= 2'b00;
        end else begin
          if (write_fifo_tx && !S_AXI_BVALID) begin
            S_AXI_BVALID <= 1'b1;
            S_AXI_BRESP  <= 2'b00;
          end else if (S_AXI_BVALID && S_AXI_BREADY) begin
            S_AXI_BVALID <= 1'b0;
          end
        end
    end
      
    always_comb S_AXI_RRESP = 2'b00;

endmodule
