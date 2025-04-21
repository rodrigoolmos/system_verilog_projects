`timescale 1ns/1ps
`include "agent_axi_lite_master.sv"

module tb_axi_lite_template_slave;

    // Parámetros del testbench         
    localparam DATA_WIDTH   = 32;                   // AXI DATA WIDTH
    localparam ADDR_WIDTH   = 32;                   // AXI ADDRESS WIDTH
    localparam CLK_PERIOD   = 10;                   // Período reloj 100 MHz
    localparam WORD_LENGHT  = (DATA_WIDTH/8);       // WORD LENGHT
    localparam NUM_DATA     = 4;


    // TB Signals
    logic [DATA_WIDTH-1:0]       send_data[NUM_DATA-1:0] = '{
                                    {32'hDEADBEEF},
                                    {32'hBAADF00D},
                                    {32'hFEEDFACE},
                                    {32'h0BADC0DE}};

    logic [DATA_WIDTH-1:0]       read_data[NUM_DATA-1:0];


    // Instancia el bus AXI
    axi_lite_if #(
        .AXI_ADDR_WIDTH(ADDR_WIDTH),
        .AXI_DATA_WIDTH(DATA_WIDTH)
    ) axi_vif();

    apb_checker #(
        .AXI_ADDR_WIDTH(ADDR_WIDTH),
        .AXI_DATA_WIDTH(DATA_WIDTH)
    ) axi_checker (
        .axi_lite(axi_vif)
    );

    // Class Agent AXI (virtual master)
    agent_AXI_m axi_master;

    //DUT
    axi_lite_template_slave # (
		.AXI_DATA_WIDTH(DATA_WIDTH),
		.AXI_ADDR_WIDTH(ADDR_WIDTH)
    ) axi_lite_template_slave_ins (
		.S_AXI_ACLK(axi_vif.S_AXI_ACLK),
		.S_AXI_ARESETN(axi_vif.S_AXI_ARESETN),
		.S_AXI_AWADDR(axi_vif.S_AXI_AWADDR),
		.S_AXI_AWPROT(axi_vif.S_AXI_AWPROT),
		.S_AXI_AWVALID(axi_vif.S_AXI_AWVALID),
		.S_AXI_AWREADY(axi_vif.S_AXI_AWREADY),
		.S_AXI_WDATA(axi_vif.S_AXI_WDATA),
		.S_AXI_WSTRB(axi_vif.S_AXI_WSTRB),
		.S_AXI_WVALID(axi_vif.S_AXI_WVALID),
		.S_AXI_WREADY(axi_vif.S_AXI_WREADY),
		.S_AXI_BRESP(axi_vif.S_AXI_BRESP),
		.S_AXI_BVALID(axi_vif.S_AXI_BVALID),
		.S_AXI_BREADY(axi_vif.S_AXI_BREADY),
		.S_AXI_ARADDR(axi_vif.S_AXI_ARADDR),
		.S_AXI_ARPROT(axi_vif.S_AXI_ARPROT),
		.S_AXI_ARVALID(axi_vif.S_AXI_ARVALID),
		.S_AXI_ARREADY(axi_vif.S_AXI_ARREADY),
		.S_AXI_RDATA(axi_vif.S_AXI_RDATA),
		.S_AXI_RRESP(axi_vif.S_AXI_RRESP),
		.S_AXI_RVALID(axi_vif.S_AXI_RVALID),
		.S_AXI_RREADY(axi_vif.S_AXI_RREADY));

    // Generación del reloj (pclk)
    initial begin
        axi_vif.S_AXI_ACLK = 0;
        forever #(CLK_PERIOD/2) axi_vif.S_AXI_ACLK = ~axi_vif.S_AXI_ACLK;
    end

    // INITIALITAION THREAD
    initial begin
        // Inicializa el bus AXI
        axi_vif.S_AXI_ACLK = 0;
        axi_vif.S_AXI_ARESETN = 0;
        axi_master = new(axi_vif);

        repeat (20) @(posedge axi_vif.S_AXI_ACLK);
        axi_vif.S_AXI_ARESETN = 1;

    end

    // PRICIPAL THREAD
    initial begin

        // Espera a que el reset se complete
        @(posedge axi_vif.S_AXI_ARESETN);
        @(posedge axi_vif.S_AXI_ACLK);

        // Realiza unas escrituras prueba
        for (int data_i=0; data_i<NUM_DATA; ++data_i) begin
            axi_master.write_AXI_data(send_data[data_i], 32'h00000000 + 
                                            data_i*WORD_LENGHT, 4'b1111);
            
        end

        // Realiza unas lecturas prueba
        for (int data_i=0; data_i<NUM_DATA; ++data_i) begin
            axi_master.read_AXI_data(read_data[data_i], 32'h00000000 + 
                                            data_i*WORD_LENGHT);
        end
        
        // Verifica que los datos leídos son correctos
        for (int data_i=0; data_i<NUM_DATA; ++data_i) begin
            assert (read_data[data_i] == send_data[data_i]) else
                $error("Error: Data mismatch at index %0d, expected %0h, got %0h",
                             data_i, send_data[data_i], read_data[data_i]);
        end

        $finish;
    end

    
endmodule