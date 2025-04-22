interface apb_if #(parameter ADDR_WIDTH = 32, DATA_WIDTH = 32);
    logic                       pclk;
    logic [ADDR_WIDTH-1:0]      paddr;
    logic [DATA_WIDTH-1:0]      pwdata;
    logic [DATA_WIDTH-1:0]      prdata;
    logic                       psel;
    logic                       pwrite;
    logic                       penable;
    logic [2:0]                 pprot;
    logic                       presetn;
    logic [DATA_WIDTH/8-1:0]    pstrb;
    logic                       pready;
    logic                       pslverr;
endinterface

class agent_APB_s #(parameter int N_REGS = 16, parameter int REGS_WIDTH = 32);
    // Virtual interface para acceder a las señales del bus APB
    virtual apb_if apb_vif;    
    logic[N_REGS-1:0] regs[REGS_WIDTH-1:0];

    // Constructor que recibe el virtual interface
    function new(virtual apb_if apb_vif);
        this.apb_vif = apb_vif;
        this.apb_vif.pready = 0;
        this.apb_vif.pslverr = 0;
        this.apb_vif.prdata = 0;
    endfunction

    // Tarea que escucha en el bus APB
    task active(int n_clk_delay = 0);
        fork
            forever begin
                this.apb_vif.pready = 0;
                @(posedge apb_vif.pclk iff
                    apb_vif.psel && apb_vif.penable);
                repeat(n_clk_delay) @(posedge apb_vif.pclk);
        
                if(apb_vif.pwrite) begin
                    if(apb_vif.paddr < N_REGS)
                        regs[apb_vif.paddr] = apb_vif.pwdata;
                    this.apb_vif.pready = 1;
                    @(posedge apb_vif.pclk);
                    this.apb_vif.pready = 0; 
                end else begin
                    if(apb_vif.paddr < N_REGS)
                        apb_vif.prdata = regs[apb_vif.paddr];
                    this.apb_vif.pready = 1;
                    @(posedge apb_vif.pclk);
                    this.apb_vif.pready = 0;
                end
            end
        join_none
    endtask

endclass