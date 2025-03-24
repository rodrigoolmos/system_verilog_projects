`timescale 1us/1ns

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


class agent_APB_m;
    // Virtual interface para acceder a las señales del bus APB
    virtual apb_if apb_vif;

    // Constructor que recibe el virtual interface
    function new(virtual apb_if apb_vif);
        this.apb_vif = apb_vif;
    endfunction

    // Tarea para escribir datos en el bus APB
    task write_APB_data(input bit [31:0] data, input bit [31:0] addr);
        apb_vif.paddr   = addr;
        apb_vif.pprot   = 0;
        apb_vif.psel    = 1;
        apb_vif.pwrite  = 1;
        apb_vif.pwdata  = data;
        apb_vif.penable = 0;
        @(posedge apb_vif.pclk);
        apb_vif.penable = 1;
        @(posedge apb_vif.pclk);
        wait(apb_vif.pready);
        apb_vif.penable = 0;
        apb_vif.psel    = 0;
        apb_vif.pwrite  = 0;
    endtask

    // Tarea para leer datos del bus APB
    task automatic read_APB_data(ref logic [31:0] data, input bit [31:0] addr);
        apb_vif.paddr   = addr;
        apb_vif.pprot   = 0;
        apb_vif.psel    = 1;
        apb_vif.pwrite  = 0;
        apb_vif.penable = 0;
        @(posedge apb_vif.pclk);
        apb_vif.penable = 1;
        @(posedge apb_vif.pclk);
        wait(apb_vif.pready);
        data = apb_vif.prdata;
        apb_vif.penable = 0;
        apb_vif.psel    = 0;
        apb_vif.pwrite  = 0;
    endtask
endclass
