`include "agent_APB_m.sv"
`timescale 1us/1ns

module tb_APB_template_slave;

    // Parámetros del testbench
    const integer t_clk    = 10;
    localparam integer N_REGS    = 8;
    localparam integer BASE_ADDR = 8;
    localparam integer DATA_WIDTH = 32;

    integer n_w_r_errors = 1;

    // Instanciamos la interfaz APB
    // Usamos DATA_WIDTH tanto para dirección como para datos (se puede ajustar según sea necesario)
    apb_if #(DATA_WIDTH, DATA_WIDTH) apb_if_inst();

    // Variable para almacenar datos leídos
    logic [DATA_WIDTH-1:0] readed_data;

    // Instanciamos el DUT (APB_template_slave)
    APB_template_slave #(
        .BASE_ADDR(BASE_ADDR),
        .DATA_WIDTH(DATA_WIDTH),
        .N_REGS(N_REGS)
    ) dut (
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
        .pslverr(apb_if_inst.pslverr)
    );

    // Instanciamos la clase APB (maestro)
    agent_APB_m apb_master;

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

    // Función monitor para verificar señales de error (pslverr)
    function void monitor();
        if ((apb_if_inst.paddr >= 4*N_REGS + BASE_ADDR) || (apb_if_inst.paddr < BASE_ADDR)) begin
            if (apb_if_inst.penable) begin
                if (!apb_if_inst.pslverr) begin
                    $display("Error: Se esperaba pslverr activado (0x%0h) con penable=%0d", apb_if_inst.pslverr, apb_if_inst.penable);
                    $stop();
                end
            end else begin
                if (apb_if_inst.pslverr) begin
                    $display("Error: pslverr=%0d se genera cuando penable=%0d no está activo", apb_if_inst.pslverr, apb_if_inst.penable);
                    $stop();
                end
            end
        end else begin
            if (apb_if_inst.pslverr) begin
                $display("Error: pslverr se genera inesperadamente (pslverr=%0d, penable=%0d)", apb_if_inst.pslverr, apb_if_inst.penable);
                $stop();
            end
        end
    endfunction

    // Secuencia de prueba
    initial begin
        // Espera al reset y luego instancia la clase APB pasando la interfaz virtual
        @(posedge apb_if_inst.presetn);
        apb_master = new(apb_if_inst);

        fork
            begin : test_sequence
                // Escrituras y lecturas continuas
                for (int i = BASE_ADDR; i < BASE_ADDR + N_REGS*4; i += 4) begin
                    apb_master.write_APB_data(i, i);
                end
                for (int i = BASE_ADDR; i < BASE_ADDR + N_REGS*4; i += 4) begin
                    apb_master.read_APB_data(readed_data, i);
                    if (readed_data !== i) begin
                        $display("Error: Dato esperado = %0d, dato leído = %0d", i, readed_data);
                        $stop;
                    end
                end
                // Escrituras y lecturas con pausas
                for (int i = BASE_ADDR; i < BASE_ADDR + N_REGS*4; i += 4) begin
                    apb_master.write_APB_data(i-BASE_ADDR, i);
                    #50 @(posedge apb_if_inst.pclk);
                end
                for (int i = BASE_ADDR; i < BASE_ADDR + N_REGS*4; i += 4) begin
                    apb_master.read_APB_data(readed_data, i);
                    #50 @(posedge apb_if_inst.pclk);
                    if (readed_data !== i-BASE_ADDR) begin
                        $display("Error: Dato esperado = %0d, dato leído = %0d", i-BASE_ADDR, readed_data);
                        $stop;
                    end
                end
                // Generar escrituras y lecturas fuera de rango
                apb_master.write_APB_data(234, BASE_ADDR - 1);
                apb_master.write_APB_data(124, BASE_ADDR + N_REGS*4);
                apb_master.read_APB_data(readed_data, BASE_ADDR - 1);
                apb_master.read_APB_data(readed_data, BASE_ADDR + N_REGS*4);
            end

            begin : error_counter
                forever begin
                    @(posedge apb_if_inst.pclk iff apb_if_inst.pslverr)
                        n_w_r_errors = n_w_r_errors + 1;
                end
            end

            begin : error_monitor
                forever begin
                    @(posedge apb_if_inst.pslverr);
                    monitor();
                end
            end
        join_any

        $display("Errores esperados en las transferencias actuales = %0d de 4", n_w_r_errors);
        $stop;
    end

endmodule
