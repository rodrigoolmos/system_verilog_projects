
`timescale 1 ns / 1 ps

module axi_lite_2_apb #
	(
		parameter integer AXI_DATA_WIDTH	= 32,
		parameter integer AXI_ADDR_WIDTH	= 4
	)
	(
		// AXI CHANNEL
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
		input   logic                               S_AXI_RREADY,	// Read ready. Master generates this signal when it accepts the read data

		// APB CHANNEL

		output  logic [AXI_ADDR_WIDTH-1:0]          PADDR,     // Dirección de la transacción
		output  logic [2:0]                			PPROT,     // Bits de protección (privilegios, cache, bufferable…)
		output  logic                      			PSEL,      // Señal de selección de este esclavo
		output  logic                      			PENABLE,   // Fase ENABLE de la transferencia APB
		output  logic                      			PWRITE,    // 1=Escritura, 0=Lectura
		output  logic [AXI_DATA_WIDTH-1:0]     		PWDATA,    // Datos de escritura al esclavo
		output  logic [(AXI_DATA_WIDTH/8)-1:0] 		PSTRB,     // Máscara de bytes válidos en la escritura
		input   logic                      			PREADY,    // 1=Transferencia completada, 0=esclavo ocupado
		input   logic [AXI_DATA_WIDTH-1:0]     		PRDATA,    // Datos de lectura desde el esclavo
		input   logic                      			PSLVERR    // 1=Error de esclavo (p.ej. dirección inválida)

	);

	logic [AXI_ADDR_WIDTH-1 : 0]        axi_awaddr;
	logic [AXI_ADDR_WIDTH-1 : 0]        axi_araddr;
	logic 								pselr;
	logic 								pselw;
	logic 								penabler;
	logic 								penablew;

	typedef enum logic[1:0] { idle_w, apb_write, wait_w } bridge_state_w_t;
	bridge_state_w_t bridge_state_w;

	typedef enum logic[1:0] { idle_r, apb_read, wait_r } bridge_state_r_t;
	bridge_state_r_t bridge_state_r;

	// ******************************* //
	// ****** WRITE GENERATION ******* //
	// ******************************* //

	// Implement of APB write generation
	always_ff @( posedge S_AXI_ACLK ) begin
	    if ( !S_AXI_ARESETN ) begin
			bridge_state_w <= idle_w;
			S_AXI_WREADY <= 0;
			S_AXI_AWREADY <= 0;
			PWDATA <= 0;
			axi_awaddr <= 0;
			pselw <= 0;
			penablew <= 0;
		end else begin
			case (bridge_state_w)
				idle_w: begin
					if (S_AXI_AWVALID && S_AXI_WVALID) begin
						bridge_state_w <= apb_write;
						pselw <= 1;
						axi_awaddr <= S_AXI_AWADDR;
						PWDATA <= S_AXI_WDATA;
					end
				end
				apb_write: begin
					penablew <= 1;
					if (PREADY) begin
						pselw <= 0;
						penablew <= 0;
						bridge_state_w <= wait_w;
						S_AXI_WREADY <= 1;
						S_AXI_AWREADY <= 1;
					end
				end
				wait_w: begin
					PWDATA <= 0;
					axi_awaddr <= 0;
					S_AXI_WREADY <= 0;
					S_AXI_AWREADY <= 0;
					if (!S_AXI_AWVALID && !S_AXI_WVALID)
						bridge_state_w <= idle_w;
				end
			endcase
	    end
	end

	always_ff @( posedge S_AXI_ACLK ) begin
	    if ( !S_AXI_ARESETN ) begin
			S_AXI_BVALID <= 0;
			S_AXI_BRESP <= 0;
		end else begin
			if (bridge_state_w == wait_w) begin
				if (!S_AXI_BVALID) begin
					S_AXI_BRESP  <= PSLVERR ? 2'b10 : 2'b00;
					S_AXI_BVALID <= 1'b1;
				end else if (S_AXI_BREADY) begin
					S_AXI_BVALID <= 1'b0;
				end
			end else begin
				S_AXI_BVALID <= 0;
			end
		end
	end


	// ******************************* //
	// ******* READ GENERATION ******* //
	// ******************************* //

	// Implement of APB read generation
	always_ff @( posedge S_AXI_ACLK ) begin
	    if ( !S_AXI_ARESETN ) begin
			bridge_state_r <= idle_r;
			S_AXI_RVALID <= 0;
			S_AXI_ARREADY <= 0;
			penabler <= 0;
			pselr <= 0;
			S_AXI_RDATA <= 0;
			S_AXI_RRESP <= 0;
			axi_araddr <= 0;
		end else begin
			case (bridge_state_r)
				idle_r: begin
					if (S_AXI_RREADY && S_AXI_ARVALID) begin
						bridge_state_r <= apb_read;
						axi_araddr <= S_AXI_ARADDR;
						pselr <= 1;
					end
				end
				apb_read: begin
					penabler <= 1;
					if (PREADY) begin
						penabler <= 0;
						pselr <= 0;
						bridge_state_r <= wait_r;
						S_AXI_RVALID <= 1;
						S_AXI_ARREADY <= 1;
						S_AXI_RDATA <= PRDATA;
						S_AXI_RRESP <= PSLVERR ? 2'b10 : 2'b00;
					end
				end
				wait_r: begin
					S_AXI_RVALID <= 0;
					S_AXI_ARREADY <= 0;
					if (!S_AXI_ARVALID && !S_AXI_RREADY) begin
						bridge_state_r <= idle_r;
						S_AXI_RDATA <= 0;
						axi_araddr <= 0;
					end
				end
			endcase
	    end
	end

	always_comb begin
		PWRITE  = S_AXI_WVALID;
		PADDR   = PWRITE ? axi_awaddr : axi_araddr;
		PSEL    = PWRITE ? pselw : pselr;
		PENABLE = PWRITE ? penablew : penabler;
		PSTRB   = S_AXI_WSTRB;
		PPROT   = PWRITE ? S_AXI_AWPROT : S_AXI_ARPROT;
	end 


endmodule
