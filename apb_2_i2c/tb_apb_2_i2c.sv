`timescale 1ns/1ps
`include "agent_i2c.sv"
`include "agent_APB_m.sv"

module tb_apb_2_i2c;

    // Parámetros del testbench
    localparam CLK_FREQ    = 100_000_000;  // 100 MHz
    localparam I2C_FREQ    = 100_000;      // 100 KHz
    localparam CLK_PERIOD  = 10;           // Período reloj 100 MHz
    localparam N_RECEPTIONS= 256;          // Número de recepciones
    localparam MSB_LSB = 1;                // 1: MSB first, 0: LSB first
    localparam BASE_ADDR = 0;            
    localparam FIFO_DEPTH = 8;             // power of 2
    localparam BITS_WAIT = 2;

    // @ddres periferal
    localparam ADDR_READ_TX_STATUS  = 5'b00000; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_WRITE_TX        = 5'b00000; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_READ_RX_STATUS  = 5'b00100; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_READ_RX_DATA    = 5'b01000; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_WRITE_N_READS   = 5'b01100; // word size 32 bits 4 bytes 2 bit @ddr
    localparam ADDR_WRITE_I2C_ADDR  = 5'b10000; // word size 32 bits 4 bytes 2 bit @ddr

    // status periferal tx/rx
    localparam logic[5:0] TRANS_OK      = 6'b100000;
    localparam logic[5:0] END_RX        = 6'b010000;
    localparam logic[5:0] FULL          = 6'b001000;
    localparam logic[5:0] ALMOST_FULL   = 6'b000100;
    localparam logic[5:0] EMPTY         = 6'b000010;
    localparam logic[5:0] ALMOST_EMPTY  = 6'b000001;
    localparam logic[5:0] NONE          = 6'b000000;

    // Data to send and receive
    logic[31:0] apb_read_data;
    logic[7:0] data_sended[N_RECEPTIONS-1:0];
    logic[7:0] data_received[N_RECEPTIONS-1:0];
    integer n_bytes_received = 0;
    integer n_bytes_sended = 0;

    // Interfaz I²C
    i2c_if i2c_vif();

    // Interfaz APB
    apb_if #(32, 32) apb_if_inst();

    // Pull-up virtual sobre la señal SDA
    pullup(i2c_vif.sda);

    // Clase Agent I²C (slave virtual)
    agent_i2c #(N_RECEPTIONS,
                7'h1A) agent_i2c_h;

    // Clase Agent APB (master virtual)
    agent_APB_m agent_APB_m_h;

    // DUT (Master)
    apb_2_i2c #(
        .MSB_LSB(MSB_LSB),
        .BASE_ADDR(BASE_ADDR),
        .FIFO_DEPTH(FIFO_DEPTH),
        .CLK_FREQ(CLK_FREQ),
        .BITS_WAIT(BITS_WAIT),
        .I2C_FREQ(I2C_FREQ)
    )apb_2_i2c_ins (
        // apb signals
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

        // spi signals
        .sda(i2c_vif.sda),
        .scl(i2c_vif.scl)
    );

    i2c_checker checker_ins(
        .i2c_vif(i2c_vif),
        .clk(apb_if_inst.pclk),
        .arstn(apb_if_inst.presetn)
    );

    function void generate_data(integer seed, logic mode);
    begin 
        for (int i=0; i<N_RECEPTIONS; ++i) begin
            if (mode) begin
                data_sended[i] = i+seed;
            end else begin
                data_sended[i] = $urandom(i+seed);
            end
        end
    end
    endfunction 

    task automatic test_empty_fifo_rx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
        assert (apb_read_data & EMPTY) 
                else begin
                    $error("APB read RX status flag is not empty");
                    $stop;
                end 

    endtask

    task automatic test_empty_fifo_tx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        assert (apb_read_data & EMPTY) 
                else $error("APB read TX status flag is not empty");
    endtask

    task automatic test_almost_empty_fifo_rx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
        assert (apb_read_data & ALMOST_EMPTY) 
                else $error("APB read RX status flag is not almost empty");
    endtask

    task automatic test_almost_empty_fifo_tx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        assert (apb_read_data & ALMOST_EMPTY) 
                else $error("APB read TX status flag is not almost empty");
    endtask

    task automatic test_full_fifo_rx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
        assert (apb_read_data & FULL) 
                else $error("APB read RX status flag is not full");
    endtask

    task automatic test_full_fifo_tx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        assert (apb_read_data & FULL) 
                else $error("APB read TX status flag is not full");
    endtask

    task automatic test_almost_full_fifo_rx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
        assert (apb_read_data & ALMOST_FULL) 
                else $error("APB read RX status flag is not almost full");
    endtask

    task automatic test_almost_full_fifo_tx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        assert (apb_read_data & ALMOST_FULL) 
                else $error("APB read TX status flag is not almost full");
    endtask

    task automatic test_none_tx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        assert (apb_read_data[3:0] == NONE)
                else begin
                    $error("APB read TX status flag NONE ERROR");
                end
    endtask

    task automatic test_none_rx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
        assert (apb_read_data[3:0] == NONE)
            else begin
                $error("APB read RX status flag NONE ERROR");
            end
    endtask

    task automatic test_end_rx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
        assert (apb_read_data & END_RX) 
                else $error("APB read RX status flag is not end");
    endtask

    task automatic test_transaction_ok_rx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
        assert (apb_read_data & TRANS_OK) 
                else $error("APB read RX status flag is not end");
    endtask

    task automatic test_transaction_ok_tx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        assert (apb_read_data & TRANS_OK) 
                else $error("APB read RX status flag is not end");
    endtask

    task automatic test_transaction_error_rx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
        assert (apb_read_data ^ TRANS_OK) 
                else $error("APB read RX status flag is not end");
    endtask
    
    task automatic test_transaction_error_tx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        assert (apb_read_data ^ TRANS_OK) 
                else $error("APB read RX status flag is not end");
    endtask

    task automatic wait_empty_fifo_tx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
        while (!(apb_read_data & EMPTY)) 
            agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_TX_STATUS);
    endtask

    task automatic wait_end_rx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
        while (!(apb_read_data & END_RX)) 
            agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
    endtask

    task automatic send_data(int n_bytes_send);
        int i;
        agent_APB_m_h.write_APB_data(0, ADDR_WRITE_N_READS);
        for(i = 0; i < n_bytes_send; i++) begin
            agent_APB_m_h.write_APB_data(data_sended[n_bytes_sended], ADDR_WRITE_TX);
            n_bytes_sended++;
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
        wait_empty_fifo_tx();
        #100000 @(posedge apb_if_inst.pclk);
    endtask

    task automatic read_sda_rx();
        agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
        while(!(apb_read_data & EMPTY)) begin
            agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_DATA);
            data_received[n_bytes_received] = apb_read_data[7:0];
            agent_APB_m_h.read_APB_data(apb_read_data, ADDR_READ_RX_STATUS);
            n_bytes_received++;
        end
    endtask 

    task automatic recive_data(int n_bytes_recive);
        int i;
        agent_APB_m_h.write_APB_data(n_bytes_recive, ADDR_WRITE_N_READS);
        wait_end_rx();
        if (n_bytes_recive == FIFO_DEPTH) begin
            test_full_fifo_rx();
        end else if (n_bytes_recive == FIFO_DEPTH -1) begin
            test_almost_full_fifo_rx();
        end else if (n_bytes_recive == 1) begin
            test_almost_empty_fifo_rx();
        end else begin
            test_none_rx();            
        end
        #100000 @(posedge apb_if_inst.pclk);
    endtask

    task automatic validate_send_receive_data();

        for (int i=0; i<N_RECEPTIONS; ++i) begin
            assert (data_received[i] == data_sended[i])
                else
                    $error("data_received %d, data_sended %d", data_received[i], data_sended[i]);
        end

    endtask 

  // Generación del reloj (pclk)
    initial begin
        apb_if_inst.pclk = 0;
        forever #(CLK_PERIOD/2) apb_if_inst.pclk = ~apb_if_inst.pclk;
    end
    
    // Inicialización de señales y reset
    initial begin
        apb_if_inst.paddr = 0;
        apb_if_inst.pprot = 0;
        apb_if_inst.psel = 0;
        apb_if_inst.penable = 0;
        apb_if_inst.pwrite = 0;
        apb_if_inst.pwdata = 0;
        apb_if_inst.pstrb = 0;
        apb_if_inst.presetn = 0;

        generate_data(0, 1);
        agent_i2c_h = new(i2c_vif, data_sended);
        agent_APB_m_h = new(apb_if_inst);

        #20 @(posedge apb_if_inst.pclk);
        apb_if_inst.presetn = 1;
    end
    
    // Hilo separado para la ejecución del agente (slave)
    initial begin
      @(posedge apb_if_inst.presetn);
      forever begin
        agent_i2c_h.i2c_slave_handle_frame();
      end
    end
    
    // Secuencia principal del test
    initial begin
        int num_bytes_receive;
        int num_bytes_send;
        int count;
        @(posedge apb_if_inst.presetn);
        #10000 @(posedge apb_if_inst.pclk);

        // SET ADDRESS WRITE
        agent_APB_m_h.write_APB_data(7'h34, ADDR_WRITE_I2C_ADDR);
        
        test_empty_fifo_rx();
        test_empty_fifo_tx();
        test_end_rx();

        $display("Start test send data");
        for (count=0; count<N_RECEPTIONS-FIFO_DEPTH; count+=num_bytes_send) begin
            num_bytes_send = $urandom_range(1, FIFO_DEPTH);
            send_data(num_bytes_send);
            test_end_rx();
            test_empty_fifo_rx();
            test_empty_fifo_tx();
            test_transaction_ok_rx();
            test_transaction_ok_tx();
        end
        send_data(N_RECEPTIONS-count);
        test_end_rx();
        test_empty_fifo_rx();
        test_empty_fifo_tx();
        test_transaction_ok_rx();
        test_transaction_ok_tx();

        // SET ADDRESS READ
        agent_APB_m_h.write_APB_data(7'h35, ADDR_WRITE_I2C_ADDR);
        $display("Start test receive data");
        for (count=0; count<N_RECEPTIONS-FIFO_DEPTH; count+=num_bytes_receive) begin
            num_bytes_receive = $urandom_range(1, FIFO_DEPTH);
            recive_data(num_bytes_receive);
            read_sda_rx();
            test_end_rx();
            test_empty_fifo_rx();
            test_empty_fifo_tx();
            test_transaction_ok_rx();
            test_transaction_ok_tx();
        end
        recive_data(N_RECEPTIONS-count);
        read_sda_rx();
        test_end_rx();
        test_empty_fifo_rx();
        test_empty_fifo_tx();
        test_transaction_ok_rx();
        test_transaction_ok_tx();

        //Generate error address write
        agent_APB_m_h.write_APB_data(7'h36, ADDR_WRITE_I2C_ADDR);
        test_transaction_error_rx();
        test_transaction_error_tx();

        //Generate error address read
        agent_APB_m_h.write_APB_data(7'h37, ADDR_WRITE_I2C_ADDR);
        test_transaction_error_rx();
        test_transaction_error_tx();

        // Validar datos enviados y recibidos
        validate_send_receive_data();
        #800000
        $finish;
    end

endmodule