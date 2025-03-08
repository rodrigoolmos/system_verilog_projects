
module APB_template_slave #(
    parameter BASE_ADDR = 8,
    parameter DATA_WIDTH = 32,  // Ancho de palabra de datos 8 16 32
    parameter N_REGS  = 8       // Número de registros < 2**32
) (
    input  logic                      pclk,     // Reloj
    input  logic                      presetn,  // Reset activo en bajo
    input  logic[31:0]                paddr,    // Direccion de escritura/lectura
    input  logic[2:0]                 pprot,    // Tipo de protección
    input  logic                      psel,     // Selección de completers
    input  logic                      penable,  // Habilita la transferencia 
    input  logic                      pwrite,   // Dirección de la transferencia: 1 para escritura, 0 para lectura
    input  logic[DATA_WIDTH-1:0]      pwdata,   // Bus de datos de escritura 8 16 32
    input  logic[(DATA_WIDTH/8)-1:0]  pstrb,    // Strobe de escritura
    output logic                      pready,   // Señal de listo 
    output logic[DATA_WIDTH-1:0]      prdata,   // Bus de datos de lectura
    output logic                      pslverr   // Error en la transferencia 
);

    const int HIGHT_ADDR = BASE_ADDR + N_REGS * 4;
    logic [DATA_WIDTH-1:0] regs [N_REGS-1:0];
    logic [31:0] addr;
    logic [29:0] reg_addr;

    // Lógica de la escritura de datos
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn)
            for (int i = 0; i < N_REGS; i++)
                regs[i] <= 0;
        else
            if (psel & pwrite & penable & ~pslverr)
                    regs[reg_addr] <= pwdata;
    end

    // calculate regs @addr
    always_comb begin
        addr = paddr-BASE_ADDR;
        reg_addr = addr[31:2];
    end

    // Señal de transferencia realizada
    always_comb pready <= penable;

    // Lógica de la lectura de datos
    always_comb prdata <= penable & ~pslverr & psel & ~pwrite ? regs[reg_addr] : 0;

    // Error en la transferencia fuera de rango
    always_comb pslverr <= ((paddr < BASE_ADDR) || (paddr >= HIGHT_ADDR)) & penable;

endmodule
