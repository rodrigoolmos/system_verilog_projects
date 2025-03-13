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
    localparam ADDR_READ_TX_STATUS  = 2'b00;
    localparam ADDR_WRITE_TX        = 2'b00;
    localparam ADDR_READ_RX_STATUS  = 2'b01;
    localparam ADDR_READ_RX_DATA    = 2'b10;

    // status periferal tx/rx
    localparam logic[3:0] FULL = 4'b1000;
    localparam logic[3:0] ALMOST_FULL = 4'b0100;
    localparam logic[3:0] EMPTY = 4'b0010;
    localparam logic[3:0] ALMOST_EMPTY = 4'b0001;

    localparam integer NUM_TRANS_RX = 16;
    localparam integer NUM_TRANS_TX = 16;

    // Instanciamos la clase APB (maestro) y uart
    agent_APB_m agent_APB_m_h;
    agent_uart#(NUM_TRANS_RX) agent_uart_h;

    // uart if
    uart_if uart_if_inst();

    // apb if
    apb_if #(32, 32) apb_if_inst();

    // data for test
    logic [7:0] data_rx_apb[NUM_TRANS_RX-1:0];
    logic [7:0] data_tx_apb[NUM_TRANS_TX-1:0];

    logic [31:0] status_apb_tx;
    logic [31:0] status_apb_rx;

    function void generate_data_tx(integer seed, logic mode);
        begin 
            for (int i=0; i<NUM_TRANS_TX; ++i) begin
                if (mode) begin
                    data_tx_apb[i] = i+seed;
                end else begin
                    data_tx_apb[i] = $urandom(i+seed);
                end
            end
        end
    endfunction 

    function void generate_data_rx(integer seed, logic mode);
        begin 
            for (int i=0; i<NUM_TRANS_RX; ++i) begin
                if (mode) begin
                    data_rx_apb[i] = i+seed;
                end else begin
                    data_rx_apb[i] = $urandom(i+seed);
                end
            end
        end
    endfunction 

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

    initial begin

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
                // Proceso APB envia datos a la uart tx
                for (int n_trans=0; n_trans<NUM_TRANS_TX; ++n_trans) begin
                    agent_APB_m_h.read_APB_data(status_apb_tx, ADDR_READ_TX_STATUS);
                    if (status_apb_tx != FULL) begin
                        agent_APB_m_h.write_APB_data(data_tx_apb[n_trans], 0);
                    end
                end
                #20ms;

                // Proceso uart rx genera transacciones en la linea rx
                for (int n_trans=0; n_trans<NUM_TRANS_RX; ++n_trans) begin
                    agent_APB_m_h.read_APB_data(status_apb_rx, ADDR_READ_RX_STATUS);
                    if (status_apb_rx != FULL) begin
                        agent_uart_h.send_data(data_rx_apb[n_trans]);
                    end
                end
                #20ms;
            end

        join_any
        $stop;
    end

endmodule