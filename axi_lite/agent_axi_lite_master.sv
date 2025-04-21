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

module apb_checker #(parameter AXI_ADDR_WIDTH = 32, 
                    parameter AXI_DATA_WIDTH = 32) 
                    (axi_lite_if axi_lite);

    property slave_init_zero;
        @(posedge axi_lite.S_AXI_ACLK)
            (axi_lite.S_AXI_ARESETN == 0) |-> 
                (axi_lite.S_AXI_AWREADY == 0 &&
                 axi_lite.S_AXI_WREADY == 0 &&
                 axi_lite.S_AXI_BRESP == 0 &&
                 axi_lite.S_AXI_BVALID == 0 &&
                 axi_lite.S_AXI_ARREADY == 0 &&
                 axi_lite.S_AXI_RDATA == 0 &&
                 axi_lite.S_AXI_RRESP == 0 &&
                 axi_lite.S_AXI_RVALID == 0);

    endproperty
    assert property (slave_init_zero)
        else $error("Slave not initialized to zero");
            
    sequence seq_A_rise_B_rise_A_fall (a, b);
        // flanco de subida de A...
        $rose(a)
        // ...espera al menos 1 ciclo y hasta infinito...
        ##[0:$]
        // ...flanco de subida de B...
        $rose(b)
        // ...y luego, en algún momento posterior, flanco de bajada de A
        ##[1:$]
        $fell(a);
    endsequence

    // Propiedad para verificar la secuencia de handshake de addr escritura
    property aw_handshake;
        @(posedge axi_lite.S_AXI_ACLK)
        seq_A_rise_B_rise_A_fall(axi_lite.S_AXI_AWVALID,
                                 axi_lite.S_AXI_AWREADY);
    endproperty
    assert property (aw_handshake);

    // Propiedad para verificar la secuencia de handshake de data escritura
    property w_handshake;
        @(posedge axi_lite.S_AXI_ACLK)
        seq_A_rise_B_rise_A_fall(axi_lite.S_AXI_WVALID,
                                 axi_lite.S_AXI_WREADY);
    endproperty
    assert property (w_handshake);
    
    // Propiedad para verificar la secuencia de handshake de addr lectura
    property ar_handshake;
        @(posedge axi_lite.S_AXI_ACLK)
        seq_A_rise_B_rise_A_fall(axi_lite.S_AXI_ARVALID,
                                 axi_lite.S_AXI_ARREADY);
    endproperty
    assert property (ar_handshake);

    // Propiedad para verificar la secuencia de handshake de data lectura
    property r_handshake;
        @(posedge axi_lite.S_AXI_ACLK)
        seq_A_rise_B_rise_A_fall(axi_lite.S_AXI_RVALID,
                                 axi_lite.S_AXI_RREADY);
    endproperty
    assert property (r_handshake);

endmodule

class agent_AXI_m;
    // Virtual interface para acceder a las señales del bus AXI
    virtual axi_lite_if axi_vif;

    // Constructor que recibe el virtual interface
    function new(virtual axi_lite_if axi_vif);
        this.axi_vif = axi_vif;
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
        assert (axi_vif.S_AXI_RRESP == 2'b00) else
            $error("AXI write failed, BRESP=%0b", axi_vif.S_AXI_RRESP);

        axi_vif.S_AXI_RREADY    = 0;
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
        assert (axi_vif.S_AXI_BRESP == 2'b00) else
            $error("AXI write failed, BRESP=%0b", axi_vif.S_AXI_BRESP);
        axi_vif.S_AXI_BREADY = 0;
    endtask
    
endclass