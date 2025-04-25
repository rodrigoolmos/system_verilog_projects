`timescale 1ns/1ps
`include "agent_axi_lite_master.sv"
`include "agent_dht22.sv"

module tb_axi_2_dht22;

    // Parámetros del testbench         
    localparam DATA_WIDTH   = 32;                   // AXI DATA WIDTH
    localparam ADDR_WIDTH   = 4 ;                   // AXI ADDRESS WIDTH
    localparam CLK_PERIOD   = 10;                   // Período reloj 100 MHz
    localparam WORD_LENGHT  = (DATA_WIDTH/8);       // WORD LENGHT
    localparam NUM_DATA     = 4;
    localparam MAX_TEST     = 40;                   // Número de test a realizar

    localparam REG_BCD_HUMIDITY     = 4'h0;
    localparam REG_BCD_TEMPERATURE  = 4'h4;
    localparam REG_CRC              = 4'h8;
    localparam REG_STATUS           = 4'hC;


    // TB Signals
    logic[15:0] data_humidity[MAX_TEST-1:0];
    logic[15:0] data_temperature[MAX_TEST-1:0];
    logic[7:0]  data_parity[MAX_TEST-1:0];
    int unsigned seed = 32'hDEADBEEF;
    logic [DATA_WIDTH-1:0]       bcd_humidity;
    logic [DATA_WIDTH-1:0]       bcd_temperature;
    logic [DATA_WIDTH-1:0]       crc;
    logic [DATA_WIDTH-1:0]       status;

    logic       error_transmission;

    // Instancia el bus AXI
    axi_lite_if #(
        .AXI_ADDR_WIDTH(ADDR_WIDTH),
        .AXI_DATA_WIDTH(DATA_WIDTH)
    ) axi_vif();

    // Instancia el bus DHT22
    dht22_if    dht22_vif();

    // Instancia el checker DHT22
    checker_dht22 checker_dht22_ins(dht22_vif, error_transmission);

    // Instancia el checker AXI
    axi_checker #(
        .AXI_ADDR_WIDTH(ADDR_WIDTH),
        .AXI_DATA_WIDTH(DATA_WIDTH)
    ) axi_checker_ins(
        .axi_lite(axi_vif)
    );

    // Class Agent AXI (virtual master)
    agent_AXI_m #(
        .AXI_ADDR_WIDTH(ADDR_WIDTH),
        .AXI_DATA_WIDTH(DATA_WIDTH)
    )axi_master;

    // Instancia el agente DHT22
    agent_dht22 agent_dht22_h;

    // Pull-up virtual sobre la señal dht22_in_out
    pullup(dht22_vif.dht22_in_out);

    //DUT
    axi_2_dht22 #(
        .CLK_FREQ(100_000_000), // 100 MHz
        .SIMULATION(1)
    ) axi_2_dht22_ins (
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
		.S_AXI_RREADY(axi_vif.S_AXI_RREADY),
        .dht22_in_out(dht22_vif.dht22_in_out)
        );

    function void correct_data_read();
        int index;
        int unsigned humidity_decimal;
        int unsigned humidity_unidades;
        int unsigned humidity_decenas;
        int unsigned temperature_decimal;
        int unsigned temperature_unidades;
        int unsigned temperature_decenas;
        logic signo_temp;

        humidity_decimal = data_humidity[index] % 10;
        humidity_unidades = (data_humidity[index] / 10) % 10;
        humidity_decenas = (data_humidity[index] / 100) % 10;

        signo_temp = data_temperature[index][15];
        temperature_decimal = data_temperature[index][14:0] % 10;
        temperature_unidades = (data_temperature[index][14:0] / 10) % 10;
        temperature_decenas = (data_temperature[index][14:0] / 100) % 10;

        if (humidity_decimal == bcd_humidity[3:0] &&
            humidity_unidades == bcd_humidity[7:4] &&
            humidity_decenas == bcd_humidity[11:8] &&
            temperature_decimal == bcd_temperature[3:0] &&
            temperature_unidades == bcd_temperature[7:4] &&
            temperature_decenas == bcd_temperature[11:8] &&
            bcd_temperature[12] == signo_temp) begin

                $display("Test passed number %0d", index);
            end else begin
                $display("Test failed"); 
                $display("SENDED ->  data_humidity: %0d %0d %0d data_temperature: %0d %0d %0d", 
                                    humidity_decimal, humidity_unidades, humidity_decenas,
                                    temperature_decimal, temperature_unidades, temperature_decenas);
                $display("RECIVED -> data_humidity: %0d %0d %0d data_temperature: %0d %0d %0d",
                        bcd_humidity[3:0],bcd_humidity[7:4],bcd_humidity[11:8],
                        bcd_temperature[3:0],bcd_temperature[7:4],bcd_temperature[11:8]);
                $display("SENDED ->  negativo_temp: %0d", signo_temp);
                $display("RECIVED -> negativo_temp: %0d", bcd_temperature[12]);
            $stop;
        end
        index++;
    endfunction
        
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
        axi_vif.S_AXI_AWADDR = 0;
        axi_vif.S_AXI_AWPROT = 0;
        axi_vif.S_AXI_AWVALID = 0;
        axi_vif.S_AXI_WDATA = 0;
        axi_vif.S_AXI_WSTRB = 0;
        axi_vif.S_AXI_WVALID = 0;
        axi_vif.S_AXI_BREADY = 0;
        axi_vif.S_AXI_ARADDR = 0;
        axi_vif.S_AXI_ARPROT = 0;
        axi_vif.S_AXI_ARVALID = 0;
        axi_vif.S_AXI_RREADY = 0;
        axi_master = new(axi_vif);
        agent_dht22_h = new(dht22_vif);

        for (int i=0; i<MAX_TEST; ++i) begin
            seed = $urandom(seed);
            data_humidity[i] = $dist_uniform(seed, 0, 999); // 0-99.9%
            seed = $urandom(seed);
            data_temperature[i][14:0] = $dist_uniform(seed, 0, 900); // -90.0-90.0°C
            seed = $urandom(seed);
            data_temperature[i][15] = $dist_uniform(seed, 0, 1); // sign
            data_parity[i] = data_humidity[i][15:8] + data_humidity[i][7:0] + 
                                data_temperature[i][15:8] + data_temperature[i][7:0];
        end

        repeat (20) @(posedge axi_vif.S_AXI_ACLK);
        axi_vif.S_AXI_ARESETN = 1;

    end
    
    // PRICIPAL THREAD
    initial begin
        error_transmission = 0;

        // Espera a que el reset se complete
        @(posedge axi_vif.S_AXI_ARESETN);
        @(posedge axi_vif.S_AXI_ACLK);
        #10ms @(posedge axi_vif.S_AXI_ACLK);

        fork
            begin // interface of control
                for (int i=0; i<MAX_TEST; ++i) begin
                    #20ms @(posedge axi_vif.S_AXI_ACLK);
                    axi_master.read_AXI_data(bcd_humidity, 32'h00000000 + REG_BCD_HUMIDITY);
                    axi_master.read_AXI_data(bcd_temperature, 32'h00000000 + REG_BCD_TEMPERATURE);
                    axi_master.read_AXI_data(crc, 32'h00000000 + REG_CRC);
                    axi_master.read_AXI_data(status, 32'h00000000 + REG_STATUS);
                    if (!error_transmission) begin
                        correct_data_read();
                        i--;
                    end
                end
            end

            begin // dth22 emulation
                for (int i=0; i<MAX_TEST/2; ++i) begin
                    agent_dht22_h.generate_dht22_data(data_humidity[i], 
                                        data_temperature[i], data_parity[i]);
                end
                error_transmission = 1;
                agent_dht22_h.generate_dht22_error(data_humidity[0], 
                                        data_temperature[0], data_parity[0]);
                error_transmission = 0;

                for (int i=MAX_TEST/2; i<MAX_TEST; ++i) begin
                    agent_dht22_h.generate_dht22_data(data_humidity[i], 
                                        data_temperature[i], data_parity[i]);
                end
            end



        join_any
        #10ms @(posedge axi_vif.S_AXI_ACLK);
        $finish;
    end

    
endmodule