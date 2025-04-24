`timescale 1 ns / 1 ps

interface axi_lite_if #(parameter AXI_ADDR_WIDTH = 32, AXI_DATA_WIDTH = 32);
    logic                                   S_AXI_ACLK;
    logic                                   S_AXI_ARESETN;
    logic [AXI_ADDR_WIDTH-1 : 0]            S_AXI_AWADDR;
    logic [2 : 0]                           S_AXI_AWPROT;
    logic                                   S_AXI_AWVALID;
    logic                                   S_AXI_AWREADY;
    logic [AXI_DATA_WIDTH-1 : 0]            S_AXI_WDATA;
    logic [(AXI_DATA_WIDTH/8)-1 : 0]        S_AXI_WSTRB;
    logic                                   S_AXI_WVALID;
    logic                                   S_AXI_WREADY;
    logic [1 : 0]                           S_AXI_BRESP;
    logic                                   S_AXI_BVALID;
    logic                                   S_AXI_BREADY;
    logic [AXI_ADDR_WIDTH-1 : 0]            S_AXI_ARADDR;
    logic [2 : 0]                           S_AXI_ARPROT;
    logic                                   S_AXI_ARVALID;
    logic                                   S_AXI_ARREADY;
    logic [AXI_DATA_WIDTH-1 : 0]            S_AXI_RDATA;
    logic [1 : 0]                           S_AXI_RRESP;
    logic                                   S_AXI_RVALID;
    logic                                   S_AXI_RREADY;
endinterface

module axi_checker #(parameter AXI_ADDR_WIDTH = 32, 
                     parameter AXI_DATA_WIDTH = 32) 
                    (axi_lite_if axi_lite);

    // AR handshake
    property ar_hs;
        @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
          $rose(axi_lite.S_AXI_ARVALID)
            |-> ##[0:$] (axi_lite.S_AXI_ARVALID && axi_lite.S_AXI_ARREADY);
    endproperty
    assert property (ar_hs)
        else $error("AR handshake failed");
      
    // AW handshake
    property aw_hs;
        @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
          $rose(axi_lite.S_AXI_AWVALID)
            |-> ##[0:$] (axi_lite.S_AXI_AWVALID && axi_lite.S_AXI_AWREADY);
    endproperty
    assert property (aw_hs)
      else $error("AW handshake failed");

    // W handshake
    property w_hs;
      @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
        $rose(axi_lite.S_AXI_WVALID)
            |-> ##[0:$] (axi_lite.S_AXI_WVALID && axi_lite.S_AXI_WREADY);
    endproperty
    assert property (w_hs)
      else $error("W handshake failed");
      
    // R data handshake (mejor disparar sobre RVALID)
    property r_hs;
      @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
        $rose(axi_lite.S_AXI_RVALID)
            |-> ##[0:$] (axi_lite.S_AXI_RVALID && axi_lite.S_AXI_RREADY);
    endproperty
    assert property (r_hs)
      else $error("R data handshake failed");
      
    // B response handshake (disparar sobre BVALID)
    property b_hs;
      @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
        $rose(axi_lite.S_AXI_BVALID)
            |-> ##[0:$] (axi_lite.S_AXI_BVALID && axi_lite.S_AXI_BREADY);
    endproperty
    assert property (b_hs)
      else $error("B response handshake failed");
                  
    // AWADDR aligned
    property aw_addr_aligned;
        @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
            axi_lite.S_AXI_AWVALID |-> (axi_lite.S_AXI_AWADDR[1:0] == 2'b00);
    endproperty
    assert property (aw_addr_aligned)
        else $error("AWADDR not aligned");

    // ARADDR aligned
    property ar_addr_aligned;
        @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
        axi_lite.S_AXI_ARVALID |-> (axi_lite.S_AXI_ARADDR[1:0] == 2'b00);
    endproperty
    assert property (ar_addr_aligned)
      else $error("ARADDR no alineado");
          
    // Correct BRESP
    property b_resp_okay;
        @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
            $rose(axi_lite.S_AXI_BVALID) |-> (axi_lite.S_AXI_BRESP == 2'b00);
    endproperty
    assert property (b_resp_okay)
        else $error("BRESP inválido: %b", axi_lite.S_AXI_BRESP);
    
    // Correct RRESP
    property r_resp_okay;
      @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
        $rose(axi_lite.S_AXI_RVALID) |-> (axi_lite.S_AXI_RRESP == 2'b00);
    endproperty
    assert property (r_resp_okay)
        else $error("RRESP inválido: %b", axi_lite.S_AXI_RRESP);
         
    // BVALID debe permanecer activo hasta que BREADY se active
    property b_valid_hold;
    @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
        (axi_lite.S_AXI_BVALID) |-> axi_lite.S_AXI_BREADY;
    endproperty
    assert property (b_valid_hold)
        else $error("BVALID deasserted befor BREADY");
                      

    // Signals stable before if S_AXI_AWVALID
    property aw_signals_stable;
    @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
        axi_lite.S_AXI_AWVALID
        |-> ##[0:$] (axi_lite.S_AXI_AWADDR  == $past(axi_lite.S_AXI_AWADDR,0)  &&
                    axi_lite.S_AXI_AWPROT  == $past(axi_lite.S_AXI_AWPROT,0)  &&
                    axi_lite.S_AXI_WDATA   == $past(axi_lite.S_AXI_WDATA,0)   &&
                    axi_lite.S_AXI_WSTRB   == $past(axi_lite.S_AXI_WSTRB,0));
    endproperty
    assert property (aw_signals_stable)
        else $error("AW signals changed before AWREADY");
          
    property b_after_aw_w;
    @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
        (axi_lite.S_AXI_AWVALID && axi_lite.S_AXI_AWREADY && axi_lite.S_AXI_WVALID && axi_lite.S_AXI_WREADY)
            |-> ##1 axi_lite.S_AXI_BVALID;
    endproperty
    assert property (b_after_aw_w)
        else $error("BVALID prematuro: falta AW/W handshake");
          
    property no_multiple_aw;
        @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
            (axi_lite.S_AXI_AWVALID && !axi_lite.S_AXI_AWREADY) |-> ##1 axi_lite.S_AXI_AWVALID;
    endproperty
    assert property (no_multiple_aw)
        else $error("AWVALID persistente tras espera de AWREADY");

    property no_multiple_ar;
        @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
            (axi_lite.S_AXI_ARVALID && !axi_lite.S_AXI_ARREADY) |-> ##1 axi_lite.S_AXI_ARVALID;
    endproperty
    assert property (no_multiple_ar)
        else $error("ARVALID persistente tras espera de ARREADY");
            
    property ar_signals_stable;
        @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
        axi_lite.S_AXI_ARVALID
            |-> ##[0:$] (
                axi_lite.S_AXI_ARADDR == $past(axi_lite.S_AXI_ARADDR) &&
                axi_lite.S_AXI_ARPROT == $past(axi_lite.S_AXI_ARPROT)
            );
    endproperty
    assert property (ar_signals_stable)
      else $error("Señales AR cambiaron antes de ARREADY");
          
    property no_multiple_w;
        @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
            (axi_lite.S_AXI_WVALID && !axi_lite.S_AXI_WREADY)
            |-> ##1 axi_lite.S_AXI_WVALID;
    endproperty
    assert property (no_multiple_w)
        else $error("WVALID no persistente tras espera de WREADY");
      
    property valid_deassert_after_hs;
        @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
            $rose(axi_lite.S_AXI_BVALID && axi_lite.S_AXI_BREADY)
            |-> ##1 !axi_lite.S_AXI_BVALID;
    endproperty
    assert property (valid_deassert_after_hs)
        else $error("BVALID no se deassert post-handshake");

    property w_signals_stable;
        @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
            axi_lite.S_AXI_WVALID
            |-> ##[0:$] (
            axi_lite.S_AXI_WDATA == $past(axi_lite.S_AXI_WDATA,0) &&
            axi_lite.S_AXI_WSTRB == $past(axi_lite.S_AXI_WSTRB,0));
    endproperty
        assert property (w_signals_stable)
            else $error("Señales W cambiaron antes de WREADY");
          
    property r_valid_hold;
        @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
            axi_lite.S_AXI_RVALID |-> axi_lite.S_AXI_RREADY;
    endproperty
    assert property (r_valid_hold)
        else $error("RVALID deasserted antes de RREADY");

    property r_signals_stable;
        @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
            axi_lite.S_AXI_RVALID
                |-> ##[0:$] (
                    axi_lite.S_AXI_RDATA == $past(axi_lite.S_AXI_RDATA,0) &&
                    axi_lite.S_AXI_RRESP == $past(axi_lite.S_AXI_RRESP,0));
    endproperty
    assert property (r_signals_stable)
        else $error("Señales R cambiaron antes de RREADY");

    property b_signals_stable;
        @(posedge axi_lite.S_AXI_ACLK) disable iff (!axi_lite.S_AXI_ARESETN)
            axi_lite.S_AXI_BVALID
                |-> ##[0:$] (
                axi_lite.S_AXI_BRESP == $past(axi_lite.S_AXI_BRESP,0));
    endproperty
    assert property (b_signals_stable)
        else $error("BRESP cambió antes de BREADY");
          
endmodule

class agent_AXI_m #(parameter AXI_ADDR_WIDTH = 32, AXI_DATA_WIDTH = 32);
    // Virtual interface para acceder a las señales del bus AXI
    virtual axi_lite_if #(
        .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH)
    ) axi_vif;

    // Constructor que recibe el virtual interface
    function new(
        virtual axi_lite_if #(
          .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
          .AXI_DATA_WIDTH(AXI_DATA_WIDTH)
        ) axi_vif_in = null
    );
        this.axi_vif = axi_vif_in;
    endfunction

    // Tarea para escribir datos en el bus AXI
    task automatic read_AXI_data(ref logic [31:0] data, input bit [31:0] addr);
        // INITIALIZE TRANSACTION
        axi_vif.S_AXI_ARADDR    = addr;
        axi_vif.S_AXI_ARVALID   = 1;
        axi_vif.S_AXI_RREADY    = 1;

        // WAIT HANDSHAKE ADDR AND DATA
        fork
            begin
                @(posedge axi_vif.S_AXI_ACLK iff axi_vif.S_AXI_ARREADY);
                axi_vif.S_AXI_ARVALID = 0;
            end
            begin
                @(posedge axi_vif.S_AXI_ACLK iff axi_vif.S_AXI_RVALID) 
                data = axi_vif.S_AXI_RDATA;
                axi_vif.S_AXI_RREADY = 0;
            end
        join
          
        data = axi_vif.S_AXI_RDATA;
        if (axi_vif.S_AXI_RRESP != 0)
            $error("AXI write failed, BRESP=%0b", axi_vif.S_AXI_RRESP);

        axi_vif.S_AXI_RREADY    = 0;
        @(posedge axi_vif.S_AXI_ACLK);
    endtask

    task write_AXI_data(input bit [31:0] data, input bit [31:0] addr, input bit[3:0] strobe);
        // INITIALIZE TRANSACTION
        axi_vif.S_AXI_AWADDR     = addr;
        axi_vif.S_AXI_WDATA      = data;
        axi_vif.S_AXI_WSTRB      = strobe;
        axi_vif.S_AXI_AWVALID    = 1;
        axi_vif.S_AXI_WVALID     = 1;
        axi_vif.S_AXI_BREADY     = 1;

        // WAIT HANDSHAKE ADDR AND DATA
        fork
            begin
                @(posedge axi_vif.S_AXI_ACLK iff axi_vif.S_AXI_AWREADY);
                axi_vif.S_AXI_AWVALID = 0;
            end
            begin
                @(posedge axi_vif.S_AXI_ACLK iff axi_vif.S_AXI_WREADY);
                axi_vif.S_AXI_WVALID = 0;
            end
        join

        // WAIT HANDSHAKE RESP AND READ RESP
        @(posedge axi_vif.S_AXI_ACLK iff axi_vif.S_AXI_BVALID);
        if (axi_vif.S_AXI_BRESP != 0)
            $error("AXI write failed, BRESP=%0b", axi_vif.S_AXI_BRESP);
        axi_vif.S_AXI_BREADY = 0;
        @(posedge axi_vif.S_AXI_ACLK);
    endtask
    
endclass