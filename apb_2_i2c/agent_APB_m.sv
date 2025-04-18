`timescale 1us/1ns

interface apb_if #(parameter ADDR_WIDTH = 32,
                   parameter DATA_WIDTH = 32);
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

module apb_checker #(ADDR_MIN = 0, ADDR_MAX = 8) (apb_if apb);
  // Aserción: Verifica que el inicio de transferencia se realice correctamente.
  property apb_transfer_start;
    @(posedge apb.pclk) disable iff (!apb.presetn)
      (apb.psel && !apb.penable) |=> (apb.psel && apb.penable);
  endproperty

  // Aserción: Verifica la generacion de error en pslverr cuando se accede a una dirección fuera del rango permitido.
  property apb_error_gen;
    @(posedge apb.pclk) disable iff (!apb.presetn)
      (apb.psel && apb.penable && apb.pready && ((apb.paddr < ADDR_MIN) || (apb.paddr > ADDR_MAX))) |-> (apb.pslverr);
  endproperty

  // Aserción: Verifica que pslverr se active solo cuando se accede a una dirección fuera del rango permitido.
  property apb_pslverr_check;
    @(posedge apb.pclk) disable iff (!apb.presetn)
      (apb.pslverr == ((apb.psel && apb.penable && (apb.paddr < ADDR_MIN || apb.paddr > ADDR_MAX)) ? 1'b1 : 1'b0));
  endproperty

  // Aserción: Verifica la estabilidad de la dirección y la señal de control de escritura durante la transferencia.
  property apb_signals_stability;
    @(posedge apb.pclk) disable iff (!apb.presetn)
      (apb.psel && apb.penable) |-> (apb.paddr == $past(apb.paddr)) && (apb.pwrite == $past(apb.pwrite));
  endproperty

  // Aserción: Verifica que, una vez iniciada la transferencia, la señal pready se active en un tiempo razonable.
  property apb_ready_handshake;
    @(posedge apb.pclk) disable iff (!apb.presetn)
      (apb.psel && apb.penable) |=> ##[1:$] apb.pready;
  endproperty

  // Aserción: Verifica que penable no se active sin que psel esté activo.
  property penable_without_psel;
    @(posedge apb.pclk) disable iff (!apb.presetn)
      (!apb.psel) |=> !apb.penable;
  endproperty

  // Instanciación de las aserciones
  a_transfer_start: assert property(apb_transfer_start)
    else begin
      $error("ERROR: Secuencia de inicio de transferencia APB fallida.");
      $stop;
    end 

  a_signals_stability: assert property(apb_signals_stability)
    else begin
      $error("ERROR: Inestabilidad en las señales APB durante la transferencia.");
      $stop;
    end

  a_ready_handshake: assert property(apb_ready_handshake)
    else begin 
      $error("ERROR: Handshake de pready no cumplido en la transferencia APB.");
      $stop;
    end

  a_penable_without_psel: assert property(penable_without_psel)
    else begin
      $error("ERROR: PENABLE activo sin PSEL en APB.");
      $stop;
    end

  a_error_gen: assert property(apb_error_gen)
    else begin
      $error("ERROR: Generación de error en PSLVERR fallida.");
      $stop;
    end
  
  a_pslverr_check: assert property(apb_pslverr_check)
    else begin
      $error("ERROR: PSLVERR no se activa correctamente.");
      $stop;
    end

endmodule


class agent_APB_m;
    // Virtual interface para acceder a las señales del bus APB
    virtual apb_if apb_vif;

    // Constructor que recibe el virtual interface
    function new(virtual apb_if apb_vif);
        this.apb_vif = apb_vif;
        this.apb_vif.psel    = 0;
        this.apb_vif.penable = 0;
        this.apb_vif.pstrb = 4'hF;
        this.apb_vif.paddr = 0;
        this.apb_vif.pprot = 0;
        this.apb_vif.pwdata = 0;
        this.apb_vif.pwrite = 0;
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
