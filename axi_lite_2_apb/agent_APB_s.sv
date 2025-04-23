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

module apb_checker #(parameter ADDR_WIDTH = 32, 
                     parameter DATA_WIDTH = 32) 
                     (apb_if apb_vif);

    // Setup phase
    // stable: PADDR PWRITE PPROT PWDATA
    property stable_signals;
        @(posedge apb_vif.pclk) disable iff (!apb_vif.presetn)
        apb_vif.psel |-> $stable(apb_vif.paddr)  &&
                         $stable(apb_vif.pwrite) &&
                         $stable(apb_vif.pprot)  &&
                         $stable(apb_vif.pstrb)  &&
                         $stable(apb_vif.pwdata);
    endproperty
    assert property (stable_signals) 
        else $error("PADDR, PWRITE, PPROT, PWDATA not stable");

    // Enable phase
    property psel_enable;
        @(posedge apb_vif.pclk) disable iff (!apb_vif.presetn)
            apb_vif.psel |=> !apb_vif.penable ##1 apb_vif.penable;
    endproperty
    assert property (psel_enable) 
        else $error("Not generating apb_vif.psel |=> !apb_vif.penable ##1 apb_vif.penable");

    // End phase
    property end_phase;
        @(posedge apb_vif.pclk) disable iff (!apb_vif.presetn)
            (apb_vif.pready && apb_vif.psel && apb_vif.penable) |=> 
                                (!apb_vif.psel && !apb_vif.penable);
    endproperty
    assert property (end_phase) 
            else $error("Not generatinf end_phase correctly");

    property no_enable_without_select;
        @(posedge apb_vif.pclk) disable iff (!apb_vif.presetn)
            apb_vif.penable |-> $past(apb_vif.psel);
    endproperty
    assert property (no_enable_without_select) 
        else $error("apb_vif.penable without apb_vif.psel");

    property setup_phase;
        @(posedge apb_vif.pclk) disable iff (!apb_vif.presetn)
            $rose(apb_vif.psel) |-> (!apb_vif.penable);
    endproperty
    assert property (setup_phase) 
        else $error("apb_vif.psel and apb_vif.penable rose at the same time");

    property pready_only_when_enable;
        @(posedge apb_vif.pclk) disable iff (!apb_vif.presetn)
            apb_vif.pready |-> apb_vif.penable;
    endproperty
    assert property (pready_only_when_enable) 
        else $error("apb_vif.pready without apb_vif.penable");

    property idle_after_end;
        @(posedge apb_vif.pclk) disable iff (!apb_vif.presetn)
            (apb_vif.psel && apb_vif.penable && apb_vif.pready) 
                |=> 
            ##[1:$] (!apb_vif.psel && !apb_vif.penable);
    endproperty
    assert property (idle_after_end) 
        else $error("Not !apb_vif.psel && !apb_vif.penable after end phase");

    property penable_implies_psel;
        @(posedge apb_vif.pclk) disable iff (!apb_vif.presetn)
            apb_vif.penable |-> apb_vif.psel;
    endproperty
    assert property (penable_implies_psel)
        else $error("PENABLE asserted without PSEL");

endmodule

class agent_APB_s #(parameter int N_REGS = 16, parameter int REGS_WIDTH = 32);
    // Virtual interface para acceder a las señales del bus APB
    virtual apb_if #(
        .ADDR_WIDTH($clog2(N_REGS)+(REGS_WIDTH/8)),
        .REGS_WIDTH(REGS_WIDTH)
    ) apb_vif; 
    logic[REGS_WIDTH-1:0] regs[N_REGS-1:0];
    int idx;

    // Constructor que recibe el virtual interface
    function new(
        virtual apb_if #(
            .ADDR_WIDTH($clog2(N_REGS)+(REGS_WIDTH/8)), 
            .REGS_WIDTH(REGS_WIDTH)
        ) apb_vif = null
    );
        this.apb_vif = apb_vif;
        this.apb_vif.pready = 0;
        this.apb_vif.pslverr = 0;
        this.apb_vif.prdata = 0;
    endfunction

    // Tarea que escucha en el bus APB
    task active(int n_clk_delay = 0);
        disable apb_read_write;
        fork : apb_read_write
            forever begin
                apb_vif.pready = 0;
                @(posedge apb_vif.pclk iff
                    apb_vif.psel && apb_vif.penable);
                repeat(n_clk_delay) @(posedge apb_vif.pclk);
                idx = apb_vif.paddr[$clog2(N_REGS)+1:2]; // word‑aligned address

                if(apb_vif.pwrite) begin
                    for (int i = 0; i < REGS_WIDTH/8; i++)
                        if (apb_vif.pstrb[i])
                            regs[idx][8*i +: 8] = apb_vif.pwdata[8*i +: 8];
                    apb_vif.pready = 1;
                    @(posedge apb_vif.pclk);
                    apb_vif.pready = 0; 
                end else begin
                    apb_vif.prdata = regs[idx];
                    apb_vif.pready = 1;
                    @(posedge apb_vif.pclk);
                    apb_vif.pready = 0;
                end
            end
        join_none
    endtask

endclass