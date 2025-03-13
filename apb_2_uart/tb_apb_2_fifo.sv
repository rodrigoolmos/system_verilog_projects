module tb_apb_2_fifo;

    const integer t_clk = 10;
    localparam integer DEPTH = 8;
    localparam integer BASE_ADDR = 8;
    localparam integer DATA_WIDTH = 32;

    localparam logic[3:0] FULL = 4'b1000;
    localparam logic[3:0] ALMOST_FULL = 4'b0100;
    localparam logic[3:0] EMPTY = 4'b0010;
    localparam logic[3:0] ALMOST_EMPTY = 4'b0001;


    integer n_w_r_errors = 1;

    // puertos
    bit                     pclk;
    bit                     presetn;
    bit[31:0]               paddr;
    bit[2:0]                pprot;
    bit                     psel;
    bit                     penable;
    bit                     pwrite;
    bit[DATA_WIDTH-1:0]     pwdata;
    bit[DATA_WIDTH/8-1:0]   pstrb;
    logic                   pready;
    logic[DATA_WIDTH-1:0]   prdata;
    logic                   pslverr;
    logic                   read_fifo_tx;
    logic                   empty_tx;
    logic                   almost_empty_tx;
    logic [DATA_WIDTH-1:0]  fifo_r_data_tx;
    logic                   write_fifo_rx;
    logic                   full_rx;
    logic                   almost_full_rx;
    logic [DATA_WIDTH-1:0]  fifo_w_data_rx;


    logic [DATA_WIDTH-1:0]  readed_apb;

    logic[DATA_WIDTH-1:0] data_send[DEPTH-1:0];
    logic[DATA_WIDTH-1:0] data_read[DEPTH-1:0];

    apb_2_fifo #(
        .BASE_ADDR(BASE_ADDR),
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(DEPTH)
    ) dut (
        .pclk(pclk),
        .presetn(presetn),
        // apb
        .paddr(paddr),
        .pprot(pprot),
        .psel(psel),
        .penable(penable),
        .pwrite(pwrite),
        .pwdata(pwdata),
        .pstrb(pstrb),
        .pready(pready),
        .prdata(prdata),
        .pslverr(pslverr),
        // fifo out tx
        .read_fifo_tx(read_fifo_tx),
        .empty_tx(empty_tx),
        .almost_empty_tx(almost_empty_tx),       
        .fifo_r_data_tx(fifo_r_data_tx),
        // fifo out rx
        .write_fifo_rx(write_fifo_rx),
        .full_rx(full_rx),
        .almost_full_rx(almost_full_rx),
        .fifo_w_data_rx(fifo_w_data_rx)
    );

    task check_integrity();
        begin 
        for (int i=0; i<DEPTH; ++i) begin
            assert(data_read[i] == data_send[i]) else $error("Error los datos enviados y leidos no cuadran %d, %d", data_read[i], data_send[i]);
        end
        end
    endtask 

    task write_APB_data(input bit[31:0] data, input bit[31:0] addr);
        paddr = addr;
        pprot = 0;
        psel = 1;
        pwrite = 1;
        pwdata = data;
        penable = 0;
        @(posedge pclk);
        penable = 1;
        @(posedge pclk);
        penable = 0;
        psel = 0;
        pwrite = 0;
    endtask

    task automatic read_APB_data(ref logic[31:0] data, input bit[31:0] addr);
        paddr = addr;
        pprot = 0;
        psel = 1;
        pwrite = 0;
        penable = 0;
        @(posedge pclk);
        penable = 1;
        @(posedge pclk);
        data = prdata;
        penable = 0;
        psel = 0;
        pwrite = 0;
    endtask

    task automatic test_fill_fifo_tx(integer seed);
        generate_data(seed, 1);
        for (int i=0; i<DEPTH; ++i) begin
            write_APB_data(data_send[i], BASE_ADDR);
            if (i==DEPTH-2) begin
                check_almost_full_tx();
            end
        end
        check_full_tx();
    endtask

    task automatic test_empty_tx_fifo();
    read_fifo_tx = 1;
        for (int i=0; i<DEPTH; ++i) begin
            @(posedge pclk);
            data_read[i] = fifo_r_data_tx;
            if (i==DEPTH-2) begin
                read_fifo_tx = 0;
                check_almost_empty_tx();
                read_fifo_tx = 1;
            end
        end
        @(posedge pclk);
        read_fifo_tx = 0;
        check_empty_tx();
    endtask

    task automatic simultaneus_read_write_tx();
        int j;
        for (int iterations=0; iterations<4; ++iterations) begin
            @(posedge pclk);
            generate_data(iterations*10, 1);
            
            fork
                begin            
                    for (int i=0; i<DEPTH; ++i) begin
                        write_APB_data(data_send[i], BASE_ADDR);
                    end
                end
                
                begin
                j=0;
                while (j<DEPTH) begin
                        wait(!empty_tx)     
                        read_fifo_tx = 1;
                        @(posedge pclk);
                        data_read[j] = fifo_r_data_tx;
                        read_fifo_tx = 0;
                        @(posedge pclk);
                        j++;
                    end
                end
            join
            check_integrity();
            @(posedge pclk);
        end
    endtask

    task test_fill_rx(integer seed, integer amount = DEPTH);
        generate_data(seed, 1);
        write_fifo_rx = 1;
        for (int i=0; i<amount; ++i) begin
            fifo_w_data_rx = data_send[i];
            @(posedge pclk);
            if (i==DEPTH-1) begin
                assert (almost_full_rx)
                    else $error("No se genera el flag de almost_full_rx de forma correcta");
            end
        end
        write_fifo_rx = 0;
        if (amount == DEPTH) begin
            @(posedge pclk);
            assert (full_rx)
                else $error("No se genera el flag de full_rx de forma correcta");
        end
    endtask 

    function void generate_data(integer seed, logic mode);
        begin 
            for (int i=0; i<DEPTH; ++i) begin
                if (mode) begin
                data_send[i] = i+seed;
                end else begin
                data_send[i] = $urandom(i+seed);
                end
            end
        end
    endfunction 

    task automatic simultaneus_read_write_rx();
        int j;
        for (int iterations=0; iterations<4; ++iterations) begin
            @(posedge pclk);
            generate_data(iterations*10, 1);
            
            fork
                begin            
                    for (int i=0; i<DEPTH; ++i) begin
                        read_APB_data(readed_apb, BASE_ADDR+4);
                        if (readed_apb != 2) begin
                            read_APB_data(readed_apb, BASE_ADDR+8);
                            data_read[i] = readed_apb;
                        end
                    end
                end
                
                begin
                j=0;
                while (j<DEPTH) begin
                        write_fifo_rx = !full_rx; 
                        fifo_w_data_rx = data_send[j];
                        @(posedge pclk);
                        j++;
                    end
		        write_fifo_rx = 0; 
                end
            join
            check_integrity();
            @(posedge pclk);
        end
    endtask

    task test_empty_rx_fifo();
        for (int i=0; i<DEPTH; ++i) begin
            read_APB_data(readed_apb, BASE_ADDR + 8);
            data_read[i] = readed_apb;
            if (i==DEPTH-2) begin
                check_almost_empty_rx();
            end
        end
        check_empty_rx();
        check_integrity();
    endtask

    task automatic check_almost_empty_rx();
        read_APB_data(readed_apb, BASE_ADDR + 4);
        assert (readed_apb == ALMOST_EMPTY)
            else $error("Almost empty rx not detected!");
    endtask

    task automatic check_empty_rx();
        read_APB_data(readed_apb, BASE_ADDR + 4);
        assert (readed_apb == EMPTY)
            else $error("Empty rx not detected!");
    endtask

    task automatic check_almost_full_rx();
        read_APB_data(readed_apb, BASE_ADDR + 4);
        assert (readed_apb == ALMOST_FULL)
            else $error("Almost full rx not detected!");
    endtask

    task automatic check_full_rx();
        read_APB_data(readed_apb, BASE_ADDR + 4);
        assert (readed_apb == FULL)
            else $error("full rx not detected!");
    endtask

    task automatic check_almost_empty_tx();
        read_APB_data(readed_apb, BASE_ADDR);
        assert (readed_apb == ALMOST_EMPTY)
            else $error("Almost empty tx not detected!");
    endtask

    task automatic check_empty_tx();
        read_APB_data(readed_apb, BASE_ADDR);
        assert (readed_apb == EMPTY)
            else $error("Empty tx not detected!");
    endtask

    task automatic check_almost_full_tx();
        read_APB_data(readed_apb, BASE_ADDR);
        assert (readed_apb == ALMOST_FULL)
            else $error("Almost full tx not detected!");
    endtask

    task automatic check_full_tx();
        read_APB_data(readed_apb, BASE_ADDR);
        assert (readed_apb == FULL)
            else $error("full tx not detected!");
    endtask

    task automatic check_pslverr(integer addr = 99999999);
        write_APB_data(32'hDEADBEEF, addr);
        assert (pslverr == 1)
            else $error("pslverr not detected!");
    endtask

    initial begin
        pclk = 0;
        forever #(t_clk/2) pclk = ~pclk;
    end

    initial begin

        write_fifo_rx = 0;
        readed_apb = 0;
        fifo_w_data_rx = 0;
        presetn = 0;
        read_fifo_tx = 0;
        #100 @ (posedge pclk);
        presetn = 1;
        @(posedge pclk);
        
        check_empty_tx();
        test_fill_fifo_tx(1);
        test_empty_tx_fifo();
        simultaneus_read_write_tx();

        check_empty_rx();
        test_fill_rx(5);
        check_full_rx();
        test_empty_rx_fifo();

        check_empty_tx();
        test_fill_fifo_tx(2);
        test_empty_tx_fifo();
        simultaneus_read_write_tx();

        check_empty_rx();
        test_fill_rx(6);
        check_full_rx();
        test_empty_rx_fifo();

        check_empty_tx();
        test_fill_fifo_tx(3);
        test_empty_tx_fifo();
        simultaneus_read_write_tx();

        check_empty_tx();
        test_fill_fifo_tx(4);
        test_empty_tx_fifo();
        simultaneus_read_write_tx();

        check_empty_rx();
        test_fill_rx(7);
        check_full_rx();
        test_empty_rx_fifo();

        check_empty_rx();
        test_fill_rx(8);
        check_full_rx();
        test_empty_rx_fifo();

        simultaneus_read_write_rx();

        test_fill_rx(11, DEPTH - 1);
        check_almost_full_rx();

        check_pslverr();
        check_pslverr(0);

        #1ns
        $stop;
    end

endmodule
