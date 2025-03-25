`include "agent_spi_s.sv"
`include "agent_APB_m.sv"

module tb_apb_2_spi;

    timeunit 1ns;
    timeprecision 1ps;

    localparam integer t_clk         = 10;
    localparam integer BASE_ADDR     = 0;
    localparam integer FIFO_DEPTH    = 16;
    localparam integer CLK_FREC      = 100000000;   // Hz
    localparam integer SCL_FREC      = 1000000;     // Hz

    localparam integer BYTE_SPI_TIME          = 8000; //ns
    localparam integer WAIT_BEFORE_SPI_TIME   = 1000; //ns
    localparam integer WAIT_AFTER_SPI_TIME    = 1000; //ns


    // @ddres periferal
    localparam ADDR_READ_TX_STATUS  = 4'b0000; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_WRITE_TX        = 4'b0000; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_READ_RX_STATUS  = 4'b0100; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_READ_RX_DATA    = 4'b1000; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_WRITE_N_READS   = 4'b1100; // word size 32 bits 4 bytes 2 bit @ddr

    // status periferal tx/rx
    localparam logic[3:0] FULL = 4'b1000;
    localparam logic[3:0] ALMOST_FULL = 4'b0100;
    localparam logic[3:0] EMPTY = 4'b0010;
    localparam logic[3:0] ALMOST_EMPTY = 4'b0001;

    localparam integer NUM_TRANS_SEND = 1024;
    localparam integer NUM_TRANS_RECEIVE = 64;

    // Instanciamos la clase APB (maestro)
    agent_APB_m agent_APB_m_h;
    // Instancia la clase SPI
    agent_spi#(NUM_TRANS_SEND) agent_spi_h;

    // data for test
    logic [7:0] data_spi_send[NUM_TRANS_SEND-1:0];
    logic [7:0] data_spi_receive[NUM_TRANS_RECEIVE-1:0];
    integer index_data_spi_send = 0;

    logic send_receive;
    logic[31:0] apb_read_data;

    // spi if
    spi_if spi_if_inst();
    // apb if
    apb_if #(32, 32) apb_if_inst();

    task wait_transfer(int n_bytes);
        int i;
        for(i = 0; i < n_bytes; i++) begin
            #1;                     // wait load byte
            #BYTE_SPI_TIME;         // wait send byte
            #WAIT_AFTER_SPI_TIME;   // wait after send byte
        end
    endtask

    task send_recive_data(int n_bytes_send, int n_bytes_recive);
        int i;
        send_receive = 0;
        agent_APB_m_h.write_APB_data(n_bytes_recive, ADDR_WRITE_N_READS);
        for(i = 0; i < n_bytes_send; i++) begin
            agent_APB_m_h.write_APB_data(i, ADDR_WRITE_TX);
        end
        wait_transfer(n_bytes_send);
        send_receive = 1;
        for(i = 0; i < n_bytes_recive; i++) begin
            agent_spi_h.send_data(i);
        end
        #WAIT_AFTER_SPI_TIME;
        send_receive = 0;
        #1000;
        @(posedge apb_if_inst.pclk);
    endtask

    task send_data(int n_bytes_send);
        int i;
        send_receive = 0;
        agent_APB_m_h.write_APB_data(0, ADDR_WRITE_N_READS);
        for(i = 0; i < n_bytes_send; i++) begin
            agent_APB_m_h.write_APB_data(data_spi_send[index_data_spi_send], ADDR_WRITE_TX);
            index_data_spi_send++;
        end
        wait_transfer(n_bytes_send);
        #1000;
        @(posedge apb_if_inst.pclk);
    endtask

    task wait_fifo_tx_empty();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        while(apb_read_data != EMPTY) begin
            @(posedge apb_if_inst.pclk);
            agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        end
    endtask

    task automatic generate_data(integer seed, logic mode,ref logic [7:0] data[NUM_TRANS_SEND-1:0]);
        begin 
            for (int i=0; i<NUM_TRANS_SEND; ++i) begin
                if (mode) begin
                    data[i] = i+seed;
                end else begin
                    data[i] = $urandom(i+seed);
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

    // Instanciamos el modulo APB a SPI
    apb_2_spi #(
        .BASE_ADDR(BASE_ADDR),
        .FIFO_DEPTH(FIFO_DEPTH),
        .CLK_FREC(CLK_FREC),
        .SCL_FREC(SCL_FREC)
    ) apb_2_spi_inst (
        .pclk(apb_if_inst.pclk),
        .presetn(apb_if_inst.presetn),
        .paddr(apb_if_inst.paddr),
        .pprot(apb_if_inst.pprot),
        .psel(apb_if_inst.psel),
        .penable(apb_if_inst.penable),
        .pwrite(apb_if_inst.pwrite),
        .pwdata(apb_if_inst.pwdata),
        .pstrb(apb_if_inst.pstrb),
        .pready(apb_if_inst.pready),
        .prdata(apb_if_inst.prdata),
        .pslverr(apb_if_inst.pslverr),
        .miso(spi_if_inst.miso),
        .mosi(spi_if_inst.mosi),
        .scl(spi_if_inst.scl),
        .cs(spi_if_inst.cs)
    );


    initial begin
        int num_bytes_send;
        agent_spi_h = new(spi_if_inst, 0);
        agent_APB_m_h = new(apb_if_inst);
        send_receive = 0;

        generate_data(12, 1, data_spi_send);

        @(posedge apb_if_inst.presetn);
        #10000 @(posedge apb_if_inst.pclk);

        fork
            // Proceso del agente: se queda recibiendo datos indefinidamente.
            begin
                forever begin
                    agent_spi_h.recive_data();
                end
            end

            begin

                // Test 1 only send data
                for (int i=0; i<10; ++i) begin
                    num_bytes_send = $urandom_range(1,16);
                    send_data(num_bytes_send);
                    wait_fifo_tx_empty();
                end
                agent_spi_h.validate_received_bytes(data_spi_send);
                
            
                //wait(spi_if_inst.cs == 1'b1);
                #10000 @(posedge apb_if_inst.pclk);
            end

        join_any
        $stop;

    end

endmodule