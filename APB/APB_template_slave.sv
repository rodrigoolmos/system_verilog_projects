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

    localparam int REG_ADDR_WIDTH = $clog2(N_REGS);
    localparam int HIGHT_ADDR = BASE_ADDR + N_REGS * 4;

    logic [DATA_WIDTH-1:0] regs [N_REGS-1:0];
    logic [31:0] addr;
    logic [REG_ADDR_WIDTH-1:0] reg_addr;

    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            for (int i = 0; i < N_REGS; i++)
                regs[i] <= i;
        end else if (psel & pwrite & penable & ~pslverr) begin
            if (reg_addr < N_REGS)
                regs[reg_addr] <= pwdata;
        end
    end

    always_comb begin
        addr = paddr - BASE_ADDR;
        reg_addr = addr[REG_ADDR_WIDTH+1:2];
    end

    always_comb pready = penable;

    always_comb prdata = (penable & ~pslverr & psel & ~pwrite && reg_addr < N_REGS) ? regs[reg_addr] : 0;

    always_comb pslverr = ((paddr < BASE_ADDR) || (paddr >= HIGHT_ADDR)) & penable;

endmodule
