module tb_APB_template_slave;

    const integer t_clk = 10;
    localparam integer N_REGS = 8;
    localparam integer BASE_ADDR = 8;
    localparam integer DATA_WIDTH = 32;

    integer n_w_r_errors = 1;

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

    logic[DATA_WIDTH-1:0]   readed_data;


    APB_template_slave #(
        .BASE_ADDR(BASE_ADDR),
        .DATA_WIDTH(DATA_WIDTH),
        .N_REGS(N_REGS)
    ) dut (
        .pclk,
        .presetn,
        .paddr,
        .pprot,
        .psel,
        .penable,
        .pwrite,
        .pwdata,
        .pstrb,
        .pready,
        .prdata,
        .pslverr
    );

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

    function void monitor();
        if ((paddr >= 4*N_REGS + BASE_ADDR) || (paddr < BASE_ADDR) ) begin
            if (penable) begin
                if (!pslverr) begin
                    $display("Error al generar pslverr = %d, penable = %d", pslverr, penable);
                    $stop();
                end
            end else begin
                if (pslverr) begin
                    $display("Error pslverr = %d se genera cuando no esta habilitado penable = %d", pslverr, penable);
                    $stop();
                end
            end
        end else begin
            if (pslverr) begin
                $display("Error pslverr se genera cuando no debe pslverr = %d, penable = %d", pslverr, penable);
                $stop();
            end
        end
    endfunction

    initial begin
        pclk = 0;
        forever #(t_clk/2) pclk = ~pclk;
    end

    initial begin

        presetn = 0;
        #100 @ (posedge pclk);
        presetn = 1;
        @(posedge pclk);

        fork            
            begin
                // escribir leer continuado
                for (int i = BASE_ADDR; i < BASE_ADDR + N_REGS*4; i+=4) begin
                    write_APB_data(i, i);
                end
                for (int i = BASE_ADDR; i < BASE_ADDR + N_REGS*4; i+=4) begin
                    read_APB_data(readed_data, i);
                    if (readed_data != i) begin
                        $display("Error en la transferencia de datos dato esperado = %d dato actual = %d", i, prdata);
                        $stop;
                    end
                end
                // escribir leer pausado
                for (int i = BASE_ADDR; i < BASE_ADDR + N_REGS*4; i+=4) begin
                    write_APB_data(i-BASE_ADDR, i);
                    #50 @(posedge pclk);
                end
                for (int i = BASE_ADDR; i < BASE_ADDR + N_REGS*4; i+=4) begin
                    read_APB_data(readed_data, i);
                    #50 @(posedge pclk);
                    if (readed_data != i-BASE_ADDR) begin
                        $display("Error en la transferencia de datos dato esperado = %d dato actual = %d", i, prdata);
                        $stop;
                    end
                end
                // generar escrituras y lecturas fuera de rengo
                write_APB_data(234, BASE_ADDR - 1);
                write_APB_data(124, BASE_ADDR + N_REGS*4);
                read_APB_data(readed_data, BASE_ADDR - 1);
                read_APB_data(readed_data, BASE_ADDR + N_REGS*4);
            end

            begin
                forever begin
                    @(posedge pclk iff pslverr)
                    n_w_r_errors = n_w_r_errors + 1;
                end
            end

            begin
                forever begin
                    @(edge pslverr);
                    monitor();
                end
            end

        join_any
        $display("Errores esperados en las transferencias 4 actuales = %d", n_w_r_errors);
        $stop;
    end

endmodule
