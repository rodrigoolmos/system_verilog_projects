`include "agent_APB_s.sv"
`include "agent_axi_lite_master.sv"

module tb_axi_2_apb;
    
    // Parámetros del testbench
    const integer      t_clk        = 10;
    localparam integer N_REGS       = 8;
    localparam integer DATA_WIDTH   = 32;
    localparam integer ADDR_WIDTH   = ($clog2(N_REGS)+(DATA_WIDTH/8));
    // Variable para almacenar datos leídos
    logic [DATA_WIDTH-1:0] readed_data;

    // Instanciamos la interfaz APB
    // Usamos DATA_WIDTH tanto para dirección como para datos (se puede ajustar según sea necesario)
    axi_lite_if #(
        .AXI_ADDR_WIDTH(ADDR_WIDTH), 
        .AXI_DATA_WIDTH(DATA_WIDTH)
    ) axi_if_inst();

    apb_if #(
        .ADDR_WIDTH(ADDR_WIDTH), 
        .DATA_WIDTH(DATA_WIDTH)
    ) apb_if_inst();

    // Instanciamos la clase AXI (maestro)
    agent_AXI_m #(
        .AXI_ADDR_WIDTH(ADDR_WIDTH), 
        .AXI_DATA_WIDTH(DATA_WIDTH)
    ) axi_master;

    // Instanciamos la clase APB (slave)
    agent_APB_s #(
        .N_REGS(N_REGS), 
        .REGS_WIDTH(DATA_WIDTH))
    apb_slave;

    axi_lite_2_apb #
	(
		.AXI_DATA_WIDTH(DATA_WIDTH),
		.AXI_ADDR_WIDTH(ADDR_WIDTH)
    )axi_lite_2_apb_ins(
		// AXI CHANNEL
		.S_AXI_ACLK(axi_if_inst.S_AXI_ACLK),        // Clock source.
		.S_AXI_ARESETN(axi_if_inst.S_AXI_ARESETN),  // Global reset source, active low.
		.S_AXI_AWADDR(axi_if_inst.S_AXI_AWADDR),    // Write address
		.S_AXI_AWPROT(axi_if_inst.S_AXI_AWPROT),    // Not used
		.S_AXI_AWVALID(axi_if_inst.S_AXI_AWVALID),  // Write address valid. Master generates this signal when Write Address and control signals are valid
		.S_AXI_AWREADY(axi_if_inst.S_AXI_AWREADY),  // Write address ready. Slave generates this signal when it can accept Write Address and control signals
		.S_AXI_WDATA(axi_if_inst.S_AXI_WDATA),      // Write data
		.S_AXI_WSTRB(axi_if_inst.S_AXI_WSTRB),      // Write strobes. 4-bit signal indicating which of the 4-bytes of Write Data. Slaves can choose assume all bytes are valid
		.S_AXI_WVALID(axi_if_inst.S_AXI_WVALID),    // Write valid. Master generates this signal when Write Data and control signals are valid
		.S_AXI_WREADY(axi_if_inst.S_AXI_WREADY),    // Write ready. Slave generates this signal when it can accept Write Data and control signals
		.S_AXI_BRESP(axi_if_inst.S_AXI_BRESP),      // Write response. 2-bit signal indicating the status of the write transaction
		.S_AXI_BVALID(axi_if_inst.S_AXI_BVALID),    // Write response valid. Slave generates this signal when the write response on the bus is valid.
		.S_AXI_BREADY(axi_if_inst.S_AXI_BREADY),    // Write response ready. Master generates this signal when it accepts the write response
		.S_AXI_ARADDR(axi_if_inst.S_AXI_ARADDR),    // Read address
		.S_AXI_ARPROT(axi_if_inst.S_AXI_ARPROT),    // Not used
		.S_AXI_ARVALID(axi_if_inst.S_AXI_ARVALID),  // Read address valid. Master generates this signal when Read Address and control signals are valid
		.S_AXI_ARREADY(axi_if_inst.S_AXI_ARREADY),  // Read address ready. Slave generates this signal when it can accept Read Address and control signals
		.S_AXI_RDATA(axi_if_inst.S_AXI_RDATA),      // Read data. Data bus for read data
		.S_AXI_RRESP(axi_if_inst.S_AXI_RRESP),      // Read response. 2-bit signal indicating the status of the read transaction
		.S_AXI_RVALID(axi_if_inst.S_AXI_RVALID),    // Read valid. Slave generates this signal when it has read data to be accepted by the master
		.S_AXI_RREADY(axi_if_inst.S_AXI_RREADY),	// Read ready. Master generates this signal when it accepts the read data

		// APB CHANNEL
		.PADDR(apb_if_inst.paddr),          // Dirección de la transacción
		.PPROT(apb_if_inst.pprot),          // Bits de protección (privilegios, cache, bufferable…)
		.PSEL(apb_if_inst.psel),            // Señal de selección de este esclavo
		.PENABLE(apb_if_inst.penable),      // Fase ENABLE de la transferencia APB
		.PWRITE(apb_if_inst.pwrite),        // 1=Escritura, 0=Lectura
		.PWDATA(apb_if_inst.pwdata),        // Datos de escritura al esclavo
		.PSTRB(apb_if_inst.pstrb),          // Máscara de bytes válidos en la escritura
		.PREADY(apb_if_inst.pready),        // 1=Transferencia completada, 0=esclavo ocupado
		.PRDATA(apb_if_inst.prdata),        // Datos de lectura desde el esclavo
		.PSLVERR(apb_if_inst.pslverr)       // 1=Error de esclavo (p.ej. dirección inválida)

	);
    
    // Generación del reloj para la interfaz APB
    initial begin
        axi_if_inst.S_AXI_ACLK = 0;
        forever #(t_clk/2) axi_if_inst.S_AXI_ACLK = ~axi_if_inst.S_AXI_ACLK;
    end

    assign apb_if_inst.pclk = axi_if_inst.S_AXI_ACLK;
    assign apb_if_inst.presetn = axi_if_inst.S_AXI_ARESETN;

    // Generación del reset
    initial begin
        axi_if_inst.S_AXI_ARESETN = 0;
        axi_if_inst.S_AXI_AWADDR = 0;
        axi_if_inst.S_AXI_AWPROT = 0;
        axi_if_inst.S_AXI_AWVALID = 0;
        axi_if_inst.S_AXI_WDATA = 0;
        axi_if_inst.S_AXI_WSTRB = 0;
        axi_if_inst.S_AXI_WVALID = 0;
        axi_if_inst.S_AXI_BREADY = 0;
        axi_if_inst.S_AXI_ARADDR = 0;
        axi_if_inst.S_AXI_ARPROT = 0;
        axi_if_inst.S_AXI_ARVALID = 0;
        axi_if_inst.S_AXI_RREADY = 0;

        apb_if_inst.pready = 0;
        apb_if_inst.prdata = 0;
        apb_if_inst.pslverr = 0;

        apb_slave = new(apb_if_inst);
        axi_master = new(axi_if_inst);
        #100 @(posedge apb_if_inst.pclk);
        axi_if_inst.S_AXI_ARESETN = 1;
        #(t_clk*10) @(posedge apb_if_inst.pclk);
    end

    // Proceso de escritura y lectura
    initial begin
        // Esperar a que el reset se complete
        @(posedge axi_if_inst.S_AXI_ARESETN);

        apb_slave.active();
        
        // Escribir datos en el bus APB
        for (int index=0; index<N_REGS; ++index) begin
            axi_master.write_AXI_data(index, (DATA_WIDTH/8)*index, 4'b1111);
        end

        // Leer datos del bus APB
        for (int index=0; index<N_REGS; ++index) begin
            axi_master.read_AXI_data(readed_data, (DATA_WIDTH/8)*index);
            assert (readed_data == index) 
            else $error("Read data mismatch: expected %0d, got %0d", index, readed_data);
        end

        // Finalizar la simulación
        #100;
        $finish;
    end

endmodule