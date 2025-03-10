module APB_template_slave #(
    parameter BASE_ADDR = 8,
    parameter DATA_WIDTH = 32,
    parameter N_REGS  = 8
) (
    input  logic                      pclk,
    input  logic                      presetn,
    input  logic [31:0]               paddr,
    input  logic [2:0]                pprot,
    input  logic                      psel,
    input  logic                      penable,
    input  logic                      pwrite,
    input  logic [DATA_WIDTH-1:0]     pwdata,
    input  logic [(DATA_WIDTH/8)-1:0] pstrb,
    output logic                      pready,
    output logic [DATA_WIDTH-1:0]     prdata,
    output logic                      pslverr
);

    localparam int REG_ADDR_WIDTH = (N_REGS > 1) ? $clog2(N_REGS) : 1;
    localparam int HIGHT_ADDR = BASE_ADDR + N_REGS * 4;

    logic [DATA_WIDTH-1:0] regs [N_REGS-1:0];
    logic [31:0] addr;
    logic [REG_ADDR_WIDTH-1:0] reg_addr;

    // Lógica segura para reg_addr
    always_comb begin
        addr = paddr - BASE_ADDR;
        if (N_REGS == 1)
            reg_addr = 0;
        else
            reg_addr = addr[REG_ADDR_WIDTH+1 : 2];
    end

    // Escritura segura con protección de rango
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            for (int i = 0; i < N_REGS; i++)
                regs[i] <= i;
        end else if (psel & pwrite & penable & ~pslverr) begin
            if (reg_addr < N_REGS)
                regs[reg_addr] <= regs[reg_addr] + pwdata;
        end
    end

    // Señal de transferencia realizada
    always_comb pready = penable;

    // Lógica de lectura protegida por rango
    always_comb prdata = (penable & ~pslverr & psel & ~pwrite && reg_addr < N_REGS) 
                          ? regs[reg_addr] : 0;

    // Error si la dirección está fuera de rango
    always_comb pslverr = ((paddr < BASE_ADDR) || (paddr >= HIGHT_ADDR)) & penable;


endmodule
