
`timescale 1 ns / 1 ps

module axi_lite_cntr #
	(
		parameter integer AXI_DATA_WIDTH	= 32,
		parameter integer AXI_ADDR_WIDTH	= 4
	)
	(
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
		input   logic                               S_AXI_RREADY,   // Read ready. Master generates this signal when it accepts the read data    
	
		input   logic [AXI_DATA_WIDTH-1:0]			bcd_humidity,
		input   logic [AXI_DATA_WIDTH-1:0]			bcd_temperature,
		input   logic [AXI_DATA_WIDTH-1:0]			crc,
		input   logic [AXI_DATA_WIDTH-1:0]			status
	
	);

	// AXI4LITE signals
	logic  	                        axi_awready;
	logic  	                        axi_wready;
	logic [1 : 0] 	                axi_bresp;
	logic  	                        axi_bvalid;
	logic [AXI_ADDR_WIDTH-1 : 0]    axi_araddr;
	logic  	                        axi_arready;
	logic [AXI_DATA_WIDTH-1 : 0]    axi_rdata;
	logic [1 : 0] 	                axi_rresp;
	logic  	                        axi_rvalid;

	// Example-specific design signals
	// local parameter for addressing 32 bit / 64 bit AXI_DATA_WIDTH
	// ADDR_LSB is used for addressing 32/64 bit registers/memories
	// ADDR_LSB = 2 for 32 bits (n downto 2)
	// ADDR_LSB = 3 for 64 bits (n downto 3)
	localparam integer ADDR_LSB = (AXI_DATA_WIDTH/32) + 1;
	localparam integer OPT_MEM_ADDR_BITS = 1;

	//----------------------------------------------
	//-- Signals for user logic register space example
	//------------------------------------------------
	//-- Number of Slave Registers 4
	logic	                    slv_reg_rden;
	logic [AXI_DATA_WIDTH-1:0]	reg_data_out;
	logic	                    aw_en;

	// I/O Connections assignments
    always_comb begin
        S_AXI_AWREADY	= axi_awready;
        S_AXI_WREADY	= axi_wready;
        S_AXI_BRESP	    = axi_bresp;
        S_AXI_BVALID	= axi_bvalid;
        S_AXI_ARREADY	= axi_arready;
        S_AXI_RDATA	    = axi_rdata;
        S_AXI_RRESP	    = axi_rresp;
        S_AXI_RVALID	= axi_rvalid;
    end

	// Implement axi_awready generation
	// axi_awready is asserted for one S_AXI_ACLK clock cycle when both
	// S_AXI_AWVALID and S_AXI_WVALID are asserted. axi_awready is
	// de-asserted when reset is low.
	always_ff @( posedge S_AXI_ACLK ) begin
	    if ( S_AXI_ARESETN == 1'b0 ) begin
	            axi_awready <= 1'b0;
	            aw_en <= 1'b1;
	    end else begin
	        if (~axi_awready && S_AXI_AWVALID && S_AXI_WVALID && aw_en) begin
	            // slave is ready to accept write address when 
	            // there is a valid write address and write data
	            // on the write address and data bus. This design 
	            // expects no outstanding transactions. 
	            axi_awready <= 1'b1;
	            aw_en <= 1'b0;
            end else if (S_AXI_BREADY && axi_bvalid) begin
	                aw_en <= 1'b1;
	                axi_awready <= 1'b0;
	        end else begin
	            axi_awready <= 1'b0;
	        end
	    end
	end

	// Implement axi_wready generation
	// axi_wready is asserted for one S_AXI_ACLK clock cycle when both
	// S_AXI_AWVALID and S_AXI_WVALID are asserted. axi_wready is 
	// de-asserted when reset is low. 
    always_ff @( posedge S_AXI_ACLK ) begin
	    if ( S_AXI_ARESETN == 1'b0 ) begin
	        axi_wready <= 1'b0;
	    end else begin    
	        if (~axi_wready && S_AXI_WVALID && S_AXI_AWVALID && aw_en ) begin
	            // slave is ready to accept write data when 
	            // there is a valid write address and write data
	            // on the write address and data bus. This design 
	            // expects no outstanding transactions. 
	            axi_wready <= 1'b1;
            end else begin
	            axi_wready <= 1'b0;
	        end
	    end 
	end


	// Implement write response logic generation
	// The write response and response valid signals are asserted by the slave 
	// when axi_wready, S_AXI_WVALID, axi_wready and S_AXI_WVALID are asserted.  
	// This marks the acceptance of address and indicates the status of 
	// write transaction.
	always_ff @( posedge S_AXI_ACLK ) begin
	    if ( S_AXI_ARESETN == 1'b0 ) begin
	        axi_bvalid  <= 0;
	        axi_bresp   <= 2'b0;
	    end else begin    
	        if (axi_awready && S_AXI_AWVALID && ~axi_bvalid && axi_wready && S_AXI_WVALID) begin
	            // indicates a valid write response is available
	            axi_bvalid <= 1'b1;
	            axi_bresp  <= 2'b0; // 'OKAY' response 
	        end else begin
	            if (S_AXI_BREADY && axi_bvalid) begin
	                //check if bready is asserted while bvalid is high) 
	                //(there is a possibility that bready is always asserted high)   
	                axi_bvalid <= 1'b0; 
	            end  
	        end
	    end
	end   

	// Implement axi_arready generation
	// axi_arready is asserted for one S_AXI_ACLK clock cycle when
	// S_AXI_ARVALID is asserted. axi_awready is 
	// de-asserted when reset (active low) is asserted. 
	// The read address is also latched when S_AXI_ARVALID is 
	// asserted. axi_araddr is reset to zero on reset assertion.

    always_ff @( posedge S_AXI_ACLK ) begin
	    if ( S_AXI_ARESETN == 1'b0 ) begin
	        axi_arready <= 1'b0;
	        axi_araddr  <= 32'b0;
	    end else begin    
	        if (~axi_arready && S_AXI_ARVALID) begin
	            // indicates that the slave has acceped the valid read address
	            axi_arready <= 1'b1;
	            // Read address latching
	            axi_araddr  <= S_AXI_ARADDR;
            end else begin
	            axi_arready <= 1'b0;
	        end
	    end 
	end       

	// Implement axi_arvalid generation
	// axi_rvalid is asserted for one S_AXI_ACLK clock cycle when both 
	// S_AXI_ARVALID and axi_arready are asserted. The slave registers 
	// data are available on the axi_rdata bus at this instance. The 
	// assertion of axi_rvalid marks the validity of read data on the 
	// bus and axi_rresp indicates the status of read transaction.axi_rvalid 
	// is deasserted on reset (active low). axi_rresp and axi_rdata are 
	// cleared to zero on reset (active low).  
    always_ff @( posedge S_AXI_ACLK ) begin
	    if ( S_AXI_ARESETN == 1'b0 ) begin
	        axi_rvalid <= 0;
	        axi_rresp  <= 0;
	    end else begin    
	        if (axi_arready && S_AXI_ARVALID && ~axi_rvalid) begin
	            // Valid read data is available at the read data bus
	            axi_rvalid <= 1'b1;
	            axi_rresp  <= 2'b0; // 'OKAY' response
	        end else if (axi_rvalid && S_AXI_RREADY) begin
	            // Read data is accepted by the master
	            axi_rvalid <= 1'b0;
	        end                
	    end
	end    

	// Implement memory mapped register select and read logic generation
	// Slave register read enable is asserted when valid address is available
	// and the slave is ready to accept the read address.
	always_comb slv_reg_rden = axi_arready & S_AXI_ARVALID & ~axi_rvalid;

	always_comb begin
	      // Address decoding for reading registers
	      case ( axi_araddr[ADDR_LSB+OPT_MEM_ADDR_BITS:ADDR_LSB] )
	        2'h0   : reg_data_out <= bcd_humidity;
	        2'h1   : reg_data_out <= bcd_temperature;
	        2'h2   : reg_data_out <= crc;
	        2'h3   : reg_data_out <= status;
	        default : reg_data_out <= 0;
	      endcase
	end

	// Output register or memory read data
    always_ff @( posedge S_AXI_ACLK ) begin
	    if ( S_AXI_ARESETN == 1'b0 ) begin
	        axi_rdata  <= 0;
        end else begin    
	        // When there is a valid read address (S_AXI_ARVALID) with 
	        // acceptance of read address by the slave (axi_arready), 
	        // output the read dada 
	        if (slv_reg_rden) begin
	            axi_rdata <= reg_data_out;     // register read data
	        end   
	    end
	end    


endmodule
