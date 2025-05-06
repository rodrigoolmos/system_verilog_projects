`include "agent_uart.sv"
`include "agent_axi_lite_master.sv"

module tb_axi_2_uart;

    timeunit 1ns;
    timeprecision 1ps;

    const integer t_clk    = 10;
    localparam integer BASE_ADDR = 0;
    localparam integer FIFO_DEPTH = 16;
    localparam integer BAUDRATE = 9600;
    localparam integer CLK_FREC = 100000000;

    // @ddres periferal
    localparam ADDR_READ_TX_STATUS  = 4'b0000; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_WRITE_TX        = 4'b0000; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_READ_RX_STATUS  = 4'b0100; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_READ_RX_DATA    = 4'b1000; // word size 32 bits 4 bytes 2 bit @ddr

    // status periferal tx/rx
    localparam logic[3:0] FULL = 4'b1000;
    localparam logic[3:0] ALMOST_FULL = 4'b0100;
    localparam logic[3:0] EMPTY = 4'b0010;
    localparam logic[3:0] ALMOST_EMPTY = 4'b0001;

    localparam integer NUM_TRANS_RX = 64;
    localparam integer NUM_TRANS_TX = 64;

    // Instanciamos la clase AXI (maestro) y uart
    agent_AXI_m agent_AXI_m_h;
    agent_uart#(NUM_TRANS_RX) agent_uart_h;

    // uart if
    uart_if uart_if_inst();

    // AXI if
    axi_lite_if #(32, 32) axi_if_inst();

    // data for test
    // sended
    logic [7:0] data_rx_uart_send[NUM_TRANS_RX-1:0];
    logic [7:0] data_tx_axi_send[NUM_TRANS_TX-1:0];
    
    // recived
    logic [7:0] data_rx_axi_recived[NUM_TRANS_RX-1:0];

    logic [31:0] data_axi_tmp;

    function void generate_data_tx(integer seed, logic mode);
        begin 
            for (int i=0; i<NUM_TRANS_TX; ++i) begin
                if (mode) begin
                    data_tx_axi_send[i] = i+seed;
                end else begin
                    data_tx_axi_send[i] = $urandom(i+seed);
                end
            end
        end
    endfunction 

    function void generate_data_rx(integer seed, logic mode);
        begin 
            for (int i=0; i<NUM_TRANS_RX; ++i) begin
                if (mode) begin
                    data_rx_uart_send[i] = i+seed;
                end else begin
                    data_rx_uart_send[i] = $urandom(i+seed);
                end
            end
        end
    endfunction 

    task empty_fifo_rx();
        static int readed_cnt;
        data_axi_tmp = FULL;
        while (data_axi_tmp != EMPTY) begin
            agent_AXI_m_h.read_AXI_data(data_axi_tmp, ADDR_READ_RX_DATA);
            data_rx_axi_recived[readed_cnt] = data_axi_tmp;
            readed_cnt++;
            agent_AXI_m_h.read_AXI_data(data_axi_tmp, ADDR_READ_RX_STATUS);
        end
    endtask

    task check_integrity_rx();
        begin 
        for (int i=0; i<NUM_TRANS_RX; ++i) begin
            assert(data_rx_axi_recived[i] == data_rx_uart_send[i]) else 
                begin
                    $error("Error los datos enviados y leidos no cuadran %d, %d", data_rx_axi_recived[i], data_rx_uart_send[i]);
                    $stop;
                end
        end
        end
    endtask 

    // Generación del reloj para la interfaz AXI
    initial begin
        axi_if_inst.S_AXI_ACLK = 0;
        forever #(t_clk/2) axi_if_inst.S_AXI_ACLK = ~axi_if_inst.S_AXI_ACLK;
    end

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

        // Se instancia los agentes
        agent_uart_h = new(uart_if_inst, BAUDRATE);
        agent_AXI_m_h = new(axi_if_inst);
        #100 @(posedge axi_if_inst.S_AXI_ACLK);
        axi_if_inst.S_AXI_ARESETN = 1;
        @(posedge axi_if_inst.S_AXI_ACLK);
    end

    axi_2_uart #(
        .BASE_ADDR(BASE_ADDR),
        .FIFO_DEPTH(FIFO_DEPTH),
        .baudrate(BAUDRATE),
        .clk_frec(CLK_FREC)
    )axi_2_uart_inst
    (
        // uart
        .rx(uart_if_inst.tx),
        .tx(uart_if_inst.rx),

        // axi
        .S_AXI_ACLK(axi_if_inst.S_AXI_ACLK),
        .S_AXI_ARESETN(axi_if_inst.S_AXI_ARESETN),
        .S_AXI_AWADDR(axi_if_inst.S_AXI_AWADDR),
        .S_AXI_AWPROT(axi_if_inst.S_AXI_AWPROT),
        .S_AXI_AWVALID(axi_if_inst.S_AXI_AWVALID),
        .S_AXI_AWREADY(axi_if_inst.S_AXI_AWREADY),
        .S_AXI_WDATA(axi_if_inst.S_AXI_WDATA),
        .S_AXI_WSTRB(axi_if_inst.S_AXI_WSTRB),
        .S_AXI_WVALID(axi_if_inst.S_AXI_WVALID),
        .S_AXI_WREADY(axi_if_inst.S_AXI_WREADY),
        .S_AXI_BRESP(axi_if_inst.S_AXI_BRESP),
        .S_AXI_BVALID(axi_if_inst.S_AXI_BVALID),
        .S_AXI_BREADY(axi_if_inst.S_AXI_BREADY),
        .S_AXI_ARADDR(axi_if_inst.S_AXI_ARADDR),
        .S_AXI_ARPROT(axi_if_inst.S_AXI_ARPROT),
        .S_AXI_ARVALID(axi_if_inst.S_AXI_ARVALID),
        .S_AXI_ARREADY(axi_if_inst.S_AXI_ARREADY),
        .S_AXI_RDATA(axi_if_inst.S_AXI_RDATA),
        .S_AXI_RRESP(axi_if_inst.S_AXI_RRESP),
        .S_AXI_RVALID(axi_if_inst.S_AXI_RVALID),
        .S_AXI_RREADY(axi_if_inst.S_AXI_RREADY)
    
    );

    axi_checker#(32, 32) axi_checker_inst(axi_if_inst);

    initial begin
        int n_trans_tx;
        int n_trans_rx;
        int wait_cycles;
        generate_data_tx(10, 1);
        generate_data_rx(100, 1);
    
        @(posedge axi_if_inst.S_AXI_ARESETN);
        repeat(10) @(posedge axi_if_inst.S_AXI_ACLK);

        fork
            // Proceso del agente: se queda recibiendo datos indefinidamente.
            begin
                forever begin
                    agent_uart_h.recive_data();
                end
            end

            begin
                // Proceso control AXI
                forever begin
                    // check if the rx fifo is full
                    agent_AXI_m_h.read_AXI_data(data_axi_tmp, ADDR_READ_RX_STATUS);
                    if (data_axi_tmp == FULL) begin
                        empty_fifo_rx();
                    end
                    
                    // send data tu fifo tx if not full
                    agent_AXI_m_h.read_AXI_data(data_axi_tmp, ADDR_READ_TX_STATUS);
                    if(n_trans_tx < NUM_TRANS_TX && data_axi_tmp != FULL) begin
                        wait_cycles = $urandom_range(wait_cycles, 10);
                        repeat (wait_cycles) @(posedge axi_if_inst.S_AXI_ACLK);
                        agent_AXI_m_h.write_AXI_data(data_tx_axi_send[n_trans_tx], ADDR_WRITE_TX, 4'b1111);
                        n_trans_tx++;
                    end

                end
            end

            begin
                // Proceso control uart envia indefinidamente
                for (n_trans_rx=0; n_trans_rx<NUM_TRANS_RX; ++n_trans_rx) begin
                    wait_cycles = $urandom_range(wait_cycles, 10);
                    repeat (wait_cycles) @(posedge axi_if_inst.S_AXI_ACLK);
                    agent_uart_h.send_data(data_rx_uart_send[n_trans_rx]);
                end
                #1ms;
            end

        join_any

        check_integrity_rx();
        agent_uart_h.validate_rx_bytes(data_tx_axi_send);

        $stop;
    end

endmodule