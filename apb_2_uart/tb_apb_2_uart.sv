`include "agent_uart.sv"
`include "agent_APB_m.sv"

module tb_apb_2_uart;

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

    // Instanciamos la clase APB (maestro) y uart
    agent_APB_m agent_APB_m_h;
    agent_uart#(NUM_TRANS_RX) agent_uart_h;

    // uart if
    uart_if uart_if_inst();

    // apb if
    apb_if #(32, 32) apb_if_inst();

    // data for test
    // sended
    logic [7:0] data_rx_uart_send[NUM_TRANS_RX-1:0];
    logic [7:0] data_tx_apb_send[NUM_TRANS_TX-1:0];
    
    // recived
    logic [7:0] data_rx_apb_recived[NUM_TRANS_RX-1:0];

    logic [31:0] data_apb_tmp;

    function void generate_data_tx(integer seed, logic mode);
        begin 
            for (int i=0; i<NUM_TRANS_TX; ++i) begin
                if (mode) begin
                    data_tx_apb_send[i] = i+seed;
                end else begin
                    data_tx_apb_send[i] = $urandom(i+seed);
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
        data_apb_tmp = FULL;
        while (data_apb_tmp != EMPTY) begin
            agent_APB_m_h.read_APB_data(data_apb_tmp, ADDR_READ_RX_DATA);
            data_rx_apb_recived[readed_cnt] = data_apb_tmp;
            readed_cnt++;
            agent_APB_m_h.read_APB_data(data_apb_tmp, ADDR_READ_RX_STATUS);
        end
    endtask

    task check_integrity_rx();
        begin 
        for (int i=0; i<NUM_TRANS_RX; ++i) begin
            assert(data_rx_apb_recived[i] == data_rx_uart_send[i]) else 
                begin
                    $error("Error los datos enviados y leidos no cuadran %d, %d", data_rx_apb_recived[i], data_rx_uart_send[i]);
                    $stop;
                end
        end
        end
    endtask 

    // Generación del reloj para la interfaz APB
    initial begin
        apb_if_inst.pclk = 0;
        forever #(t_clk/2) apb_if_inst.pclk = ~apb_if_inst.pclk;
    end

    // Generación del reset
    initial begin
        apb_if_inst.presetn = 0;
        #100 @(posedge apb_if_inst.pclk);
        apb_if_inst.presetn = 1;
        @(posedge apb_if_inst.pclk);
    end

    apb_2_uart #(
        .BASE_ADDR(BASE_ADDR),
        .FIFO_DEPTH(FIFO_DEPTH),
        .baudrate(BAUDRATE),
        .clk_frec(CLK_FREC)
    )apb_2_uart_inst
    (
        .clk(apb_if_inst.pclk),
        .arstn(apb_if_inst.presetn),

        // uart
        .rx(uart_if_inst.tx),
        .tx(uart_if_inst.rx),

        // apb
        .paddr(apb_if_inst.paddr),
        .pprot(apb_if_inst.pprot),
        .psel(apb_if_inst.psel),
        .penable(apb_if_inst.penable),
        .pwrite(apb_if_inst.pwrite),
        .pwdata(apb_if_inst.pwdata),
        .pstrb(apb_if_inst.pstrb),
        .pready(apb_if_inst.pready),
        .prdata(apb_if_inst.prdata),
        .pslverr(apb_if_inst.pslverr)
    );

    apb_checker apb_checker_inst(apb_if_inst);

    initial begin
        int n_trans_tx;
        int n_trans_rx;
        int wait_cycles;
        generate_data_tx(0, 1);
        generate_data_rx(100, 1);

        // Se instancia los agentes
        agent_uart_h = new(uart_if_inst, BAUDRATE);
        agent_APB_m_h = new(apb_if_inst);
    
        @(posedge apb_if_inst.presetn);
        repeat(10) @(posedge apb_if_inst.pclk);

        fork
            // Proceso del agente: se queda recibiendo datos indefinidamente.
            begin
                forever begin
                    agent_uart_h.recive_data();
                end
            end

            begin
                // Proceso control APB
                forever begin
                    // check if the rx fifo is full
                    agent_APB_m_h.read_APB_data(data_apb_tmp, ADDR_READ_RX_STATUS);
                    if (data_apb_tmp == FULL) begin
                        empty_fifo_rx();
                    end
                    
                    // send data tu fifo tx if not full
                    agent_APB_m_h.read_APB_data(data_apb_tmp, ADDR_READ_TX_STATUS);
                    if(n_trans_tx < NUM_TRANS_TX && data_apb_tmp != FULL) begin
                        wait_cycles = $urandom_range(wait_cycles, 10);
                        repeat (wait_cycles) @(posedge apb_if_inst.pclk);
                        agent_APB_m_h.write_APB_data(data_tx_apb_send[n_trans_tx], ADDR_WRITE_TX);
                        n_trans_tx++;
                    end

                end
            end

            begin
                // Proceso control uart envia indefinidamente
                for (n_trans_rx=0; n_trans_rx<NUM_TRANS_RX; ++n_trans_rx) begin
                    wait_cycles = $urandom_range(wait_cycles, 10);
                    repeat (wait_cycles) @(posedge apb_if_inst.pclk);
                    agent_uart_h.send_data(data_rx_uart_send[n_trans_rx]);
                end
                #1ms;
            end

        join_any

        check_integrity_rx();
        agent_uart_h.validate_rx_bytes(data_tx_apb_send);

        $stop;
    end

endmodule