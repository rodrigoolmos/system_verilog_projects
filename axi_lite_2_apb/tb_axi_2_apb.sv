`include "agent_APB_m.sv"
`include "agent_APB_s.sv"

module tb_axi_2_apb;
    
    // Parámetros del testbench
    const integer t_clk    = 10;
    localparam integer N_REGS    = 8;
    localparam integer DATA_WIDTH = 32;

    // Instanciamos la interfaz APB
    // Usamos DATA_WIDTH tanto para dirección como para datos (se puede ajustar según sea necesario)
    apb_if #(DATA_WIDTH, DATA_WIDTH) apb_if_inst();

    // Variable para almacenar datos leídos
    logic [DATA_WIDTH-1:0] readed_data;

    // Instanciamos la clase APB (maestro)
    agent_APB_m apb_master;

    // Instanciamos la clase APB (slave)
    agent_APB_s #(
        .N_REGS(N_REGS), 
        .REGS_WIDTH(DATA_WIDTH))
    apb_slave;

    // Generación del reloj para la interfaz APB
    initial begin
        apb_if_inst.pclk = 0;
        forever #(t_clk/2) apb_if_inst.pclk = ~apb_if_inst.pclk;
    end

    // Generación del reset
    initial begin
        apb_if_inst.presetn = 0;
        apb_if_inst.paddr = 0;
        apb_if_inst.pprot = 0;
        apb_if_inst.psel = 0;
        apb_if_inst.penable = 0;
        apb_if_inst.pwrite = 0;
        apb_if_inst.pwdata = 0;
        apb_if_inst.pstrb = 0;
        apb_slave = new(apb_if_inst);
        apb_master = new(apb_if_inst);
        #100 @(posedge apb_if_inst.pclk);
        apb_if_inst.presetn = 1;
        #(t_clk*10) @(posedge apb_if_inst.pclk);
    end

    // Proceso de escritura y lectura
    initial begin
        // Esperar a que el reset se complete
        @(posedge apb_if_inst.presetn);

        apb_slave.active();
        
        // Escribir datos en el bus APB
        apb_master.write_APB_data(32'hDEADBEEF, 32'h00000000);
        apb_master.write_APB_data(32'hCAFEBABE, 32'h00000004);

        // Leer datos del bus APB
        apb_master.read_APB_data(readed_data, 32'h00000000);
        $display("Read data: %h", readed_data);

        apb_master.read_APB_data(readed_data, 32'h00000004);
        $display("Read data: %h", readed_data);

        // Finalizar la simulación
        #100;
        $finish;
    end

endmodule