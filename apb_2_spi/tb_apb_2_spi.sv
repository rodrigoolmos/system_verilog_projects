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
    localparam logic[3:0] NONE = 4'b0000;

    localparam integer MSB_LSB = 1;

    localparam integer NUM_TRANS = 2048;

    // Instanciamos la clase APB (maestro)
    agent_APB_m agent_APB_m_h;
    // Instancia la clase SPI
    agent_spi#(NUM_TRANS) agent_spi_h;

    // data for test
    logic [7:0] data_spi_mosi_send[NUM_TRANS-1:0];
    logic [7:0] data_spi_miso_receive[NUM_TRANS-1:0];
    logic [7:0] data_spi_miso_readed[NUM_TRANS-1:0];
    integer index_data_spi_send = 0;
    integer index_data_spi_receive = 0;

    logic send = 0;
    logic receive = 0;
    logic[1:0] num_test = 0;
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

    task automatic send_recive_data(int n_bytes_send, int n_bytes_recive);
        int i;
        send = 1;
        agent_APB_m_h.write_APB_data(n_bytes_recive, ADDR_WRITE_N_READS);
        for(i = 0; i < n_bytes_send; i++) begin
            agent_APB_m_h.write_APB_data(data_spi_mosi_send[index_data_spi_send], ADDR_WRITE_TX);
            index_data_spi_send++;
        end
        if (n_bytes_send == FIFO_DEPTH) begin
            test_full_fifo_tx();
        end else if (n_bytes_send == FIFO_DEPTH -1) begin
            test_almost_full_fifo_tx();
        end else if (n_bytes_send == 1) begin
            test_almost_empty_fifo_tx();
        end else begin
            test_none_tx();   
        end
        wait_transfer(n_bytes_send);
        send = 0;
        receive = 1;
        for(i = 0; i < n_bytes_recive; i++) begin
            agent_spi_h.send_data(data_spi_miso_receive[index_data_spi_receive]);
            index_data_spi_receive ++;
        end
        #WAIT_AFTER_SPI_TIME;
        receive = 0;
        wait(spi_if_inst.cs);
        #100000 @(posedge apb_if_inst.pclk);
        if (n_bytes_recive == FIFO_DEPTH) begin
            test_full_fifo_rx();
        end else if (n_bytes_recive == FIFO_DEPTH -1) begin
            test_almost_full_fifo_rx();
        end else if (n_bytes_recive == 1) begin
            test_almost_empty_fifo_rx();
        end else begin
            test_none_rx();   
        end
    endtask

    task automatic send_data(int n_bytes_send);
        int i;
        send = 1;
        agent_APB_m_h.write_APB_data(0, ADDR_WRITE_N_READS);
        for(i = 0; i < n_bytes_send; i++) begin
            agent_APB_m_h.write_APB_data(data_spi_mosi_send[index_data_spi_send], ADDR_WRITE_TX);
            index_data_spi_send++;
        end
        if (n_bytes_send == FIFO_DEPTH) begin
            test_full_fifo_tx();
        end else if (n_bytes_send == FIFO_DEPTH -1) begin
            test_almost_full_fifo_tx();
        end else if (n_bytes_send == 1) begin
            test_almost_empty_fifo_tx();
        end else begin
            test_none_tx();   
        end
        wait_transfer(n_bytes_send);
        wait(spi_if_inst.cs);
        send = 0;
        #100000 @(posedge apb_if_inst.pclk);
    endtask

    task automatic recive_data(int n_bytes_recive);
        int i;
        agent_APB_m_h.write_APB_data(n_bytes_recive, ADDR_WRITE_N_READS);
        receive = 1;
        for(i = 0; i < n_bytes_recive; i++) begin
            agent_spi_h.send_data(data_spi_miso_receive[index_data_spi_receive]);
            index_data_spi_receive ++;
        end
        #WAIT_AFTER_SPI_TIME;
        receive = 0;
        wait(spi_if_inst.cs);
        #100000 @(posedge apb_if_inst.pclk);
        if (n_bytes_recive == FIFO_DEPTH) begin
            test_full_fifo_rx();
        end else if (n_bytes_recive == FIFO_DEPTH -1) begin
            test_almost_full_fifo_rx();
        end else if (n_bytes_recive == 1) begin
            test_almost_empty_fifo_rx();
        end else begin
            test_none_rx();            
        end
    endtask

    task wait_fifo_tx_empty();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        while(apb_read_data[3:0] != EMPTY) begin
            @(posedge apb_if_inst.pclk);
            agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        end
    endtask

    task generate_error_pslverr();
        agent_APB_m_h.write_APB_data(8'h12, 32'hDEADBEEF);
        agent_APB_m_h.read_APB_data(apb_read_data, 32'hBEEFDEAD);
    endtask

    task automatic generate_data(integer seed, logic mode,ref logic [7:0] data[NUM_TRANS-1:0]);
        begin 
            for (int i=0; i<NUM_TRANS; ++i) begin
                if (mode) begin
                    data[i] = i+seed;
                end else begin
                    data[i] = $urandom(i+seed);
                end
            end
        end
    endtask 

    task automatic read_mosi_rx();
        static int i;
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
        while(apb_read_data[3:0] != EMPTY) begin
            agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_DATA);
            data_spi_miso_readed[i] = apb_read_data[7:0];
            agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
            i++;
        end
    endtask 

    task automatic validate_read_miso_rx();
        $display("Num bytes readed by the master %d", index_data_spi_receive);

        for (int i=0; i<index_data_spi_receive; ++i) begin
            assert (data_spi_miso_readed[i] == data_spi_miso_receive[i])
                else   begin
                    $error("Error: data readed is not equal to data received numeber of byte %d", i);
                    $error("Received %d, expected %d", data_spi_miso_readed[i], data_spi_miso_receive[i]);
                 end
        end

    endtask 

    task automatic test_empty_fifo_rx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
        assert (apb_read_data[3:0] == EMPTY) 
                else $error("APB read RX status flag is not empty");
    endtask

    task automatic test_empty_fifo_tx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        assert (apb_read_data[3:0] == EMPTY) 
                else $error("APB read TX status flag is not empty");
    endtask

    task automatic test_almost_empty_fifo_rx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
        assert (apb_read_data[3:0] == ALMOST_EMPTY) 
                else $error("APB read RX status flag is not almost empty");
    endtask

    task automatic test_almost_empty_fifo_tx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        assert (apb_read_data[3:0] == ALMOST_EMPTY) 
                else $error("APB read TX status flag is not almost empty");
    endtask

    task automatic test_full_fifo_rx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
        assert (apb_read_data[3:0] == FULL) 
                else $error("APB read RX status flag is not full");
    endtask

    task automatic test_full_fifo_tx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        assert (apb_read_data[3:0] == FULL) 
                else $error("APB read TX status flag is not full");
    endtask

    task automatic test_almost_full_fifo_rx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
        assert (apb_read_data[3:0] == ALMOST_FULL) 
                else $error("APB read RX status flag is not almost full");
    endtask

    task automatic test_almost_full_fifo_tx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        assert (apb_read_data[3:0] == ALMOST_FULL) 
                else $error("APB read TX status flag is not almost full");
    endtask

    task automatic test_none_tx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        assert (apb_read_data[3:0] == NONE) 
                else $error("APB read TX status flag NONE ERROR");
    endtask

    task automatic test_none_rx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
        assert (apb_read_data[3:0] == NONE) 
                else $error("APB read RX status flag NONE ERROR");
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
        .MSB_LSB(MSB_LSB), // 1: MSB first, 0: LSB first
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

    spi_checker#(
        .CLK_FREC(CLK_FREC),
        .SCL_FREC(SCL_FREC)
    )spi_checker_ins(
        .spi(spi_if_inst),
        .send(send),
        .clk(apb_if_inst.pclk),
        .arstn(apb_if_inst.presetn)
    );

    apb_checker 
            #(.ADDR_MIN(0), 
              .ADDR_MAX(12)
            ) apb_checker_ins (.apb(apb_if_inst));

    initial begin
        int num_bytes_send;
        int lotery;
        int num_bytes_receive;
        agent_spi_h = new(spi_if_inst);
        agent_APB_m_h = new(apb_if_inst);
        agent_spi_h.set_msb_lsb(MSB_LSB);

        generate_data(0, 1, data_spi_mosi_send);
        generate_data(0, 1, data_spi_miso_receive);

        @(posedge apb_if_inst.presetn);
        #10000 @(posedge apb_if_inst.pclk);

        fork
            // Proceso del agente: se queda recibiendo datos indefinidamente.
            begin
                forever begin
                    agent_spi_h.recive_data(send);
                end
            end

            begin

                test_empty_fifo_rx();
                test_empty_fifo_tx();

                // Test 1 only send data
                num_test = 1;
                $display("Start test send data");
                for (int i=0; i<30; ++i) begin
                    num_bytes_send = $urandom_range(1, FIFO_DEPTH);
                    send_data(num_bytes_send);
                    wait_fifo_tx_empty();
                end
                send_data(FIFO_DEPTH);                              // send FIFO_DEPTH bytes 
                wait_fifo_tx_empty();
                send_data(FIFO_DEPTH-1);                            // send FIFO_DEPTH - 1 bytes 
                wait_fifo_tx_empty();
                agent_spi_h.validate_received_bytes(data_spi_mosi_send, index_data_spi_send);  // validate data received by the slave MOSI send data
                
                // // Test 2 only receive data
                num_test = 2;
                $display("Start test receive data");
                for (int i=0; i<30; ++i) begin
                    num_bytes_receive = $urandom_range(1, FIFO_DEPTH);
                    recive_data(num_bytes_receive);
                    read_mosi_rx();
                end
                recive_data(FIFO_DEPTH);                            // receive FIFO_DEPTH bytes
                read_mosi_rx();
                recive_data(FIFO_DEPTH-1);                          // receive FIFO_DEPTH -1 bytes
                read_mosi_rx();
                validate_read_miso_rx();                            // validate data received by the master MISO send data

                // Test 3 send and receive data
                num_test = 3;
                $display("Start test send and receive data");
                for (int i=0; i<30; ++i) begin
                    num_bytes_send = $urandom_range(1, FIFO_DEPTH);
                    num_bytes_receive = $urandom_range(1, FIFO_DEPTH);
                    send_recive_data(num_bytes_send, num_bytes_receive);
                    read_mosi_rx();
                end
                send_recive_data(FIFO_DEPTH, FIFO_DEPTH);           // send and receive FIFO_DEPTH bytes
                read_mosi_rx();
                send_recive_data(FIFO_DEPTH-1, FIFO_DEPTH-1);           // send and receive FIFO_DEPTH bytes
                read_mosi_rx();
                validate_read_miso_rx();                                                        // validate data received by the master MISO send data
                agent_spi_h.validate_received_bytes(data_spi_mosi_send, index_data_spi_send);   // validate data received by the slave MOSI send data

                // Test 4 random send and receive data
                num_test = 4;
                $display("Start test random send and receive data lotery");
                for (int i=0; i<30; ++i) begin
                    lotery = $urandom_range(1, 4);
                    if (lotery == 1) begin
                        num_bytes_send = $urandom_range(1, FIFO_DEPTH);
                        send_data(num_bytes_send);
                        wait_fifo_tx_empty();
                    end else if (lotery == 2) begin
                        num_bytes_receive = $urandom_range(1, FIFO_DEPTH);
                        recive_data(num_bytes_receive);
                        read_mosi_rx();
                    end else if (lotery == 3) begin
                        num_bytes_send = $urandom_range(1, FIFO_DEPTH);
                        num_bytes_receive = $urandom_range(1, FIFO_DEPTH);
                        send_recive_data(num_bytes_send, num_bytes_receive);
                        read_mosi_rx();
                    end else begin
                        generate_error_pslverr();
                    end
                end
                validate_read_miso_rx();                                                        // validate data received by the master MISO send data
                agent_spi_h.validate_received_bytes(data_spi_mosi_send, index_data_spi_send);   // validate data received by the slave MOSI send data


                num_test = 0;
                generate_error_pslverr();

                #10000 @(posedge apb_if_inst.pclk);
            end

        join_any
        $stop;

    end

endmodule