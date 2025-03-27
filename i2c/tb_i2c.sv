`timescale 1ns/1ps
module tb_i2c;

  // Parámetros para el testbench
  localparam CLK_FREQ  = 100_000_000;  // 100 MHz
  localparam I2C_FREQ  = 100_000;      // 100 KHz
  localparam CLK_PERIOD = 10;          // Período de reloj en ns (para 100 MHz)

  // Señales de prueba
  logic clk;
  logic arstn;
  logic [7:0] byte_2_send;
  logic [7:0] byte_received;
  logic ena_i2c;
  logic end_trans;
  logic msb_lsb;
  logic [7:0] adrr_r_w;
  tri sda;
  logic scl;

  // datos recividos
  logic [7:0] data_received_slave;
  logic [7:0] data_sended_slave;
  logic [7:0] addres_received_slave;


  // Instanciación del DUT
  i2c #(
      .CLK_FREQ(CLK_FREQ),
      .I2C_FREQ(I2C_FREQ)
  ) dut (
      .clk(clk),
      .arstn(arstn),
      .byte_2_send(byte_2_send),
      .byte_received(byte_received),
      .ena_i2c(ena_i2c),
      .end_trans(end_trans),
      .msb_lsb(msb_lsb),
      .adrr_r_w(adrr_r_w),
      .sda(sda),
      .scl(scl)
  );

  // Generación de reloj
  initial begin
    clk = 0;
    forever #(CLK_PERIOD/2) clk = ~clk;
  end

  // Generación de reset
  initial begin
    arstn = 0;
    #20;      // Mantener el reset por 20 ns
    arstn = 1;
  end

  // Estímulo inicial
  initial begin
    // Inicialización de señales
    ena_i2c    = 0;
    msb_lsb    = 1;             // Suponiendo que '1' es MSB primero
    adrr_r_w   = 8'hA0;         // Ejemplo de dirección (7-bit + bit R/W)
    byte_2_send = 8'h55;        // Ejemplo de byte a enviar
    data_sended_slave = 8'hFE;  // Ejemplo de byte a enviar
    
    // Esperar al final del reset
    @(posedge arstn);
    #20;
    
    // Iniciar la transacción I2C
    ena_i2c = 1;

    // Esperar a que la transacción termine
    repeat(2) @(posedge end_trans);  
    
    // Se puede agregar más estímulo para verificar distintas condiciones
    #1000;
    ena_i2c = 0;
    #100000;
    

    adrr_r_w   = 8'hA1;      // Ejemplo de dirección (7-bit + bit R/W)
    byte_2_send = 8'h00;     // Ejemplo de byte a enviar
    
    // Iniciar la transacción I2C
    ena_i2c = 1;

    // Esperar a que la transacción termine
    repeat(2) @(posedge end_trans);  
    
    // Se puede agregar más estímulo para verificar distintas condiciones
    #1000;
    ena_i2c = 0;
    #10000;

    // Finalizar simulación tras un tiempo adicional
    #40000;
    $finish;
  end

  // Monitor opcional para observar señales en la simulación
  initial begin
    forever begin
      release sda;
      // START CONDITION
      @(negedge sda iff scl); 
  
      // ADDRES TRANSMISION
      for (int i=0; i<8; ++i) begin
        @(posedge scl);
        if (msb_lsb) begin
          addres_received_slave[7-i] = sda;
        end else begin
          addres_received_slave[i] = sda;
        end
      end
  
      // ACK
      @(negedge scl);
      #1000;
      force sda  = 1'b0;
      @(negedge scl);
      release sda;
  
      // DATA TRANSMISION
      if (!addres_received_slave[0]) begin     // Si es una escritura
        for (int i=0; i<8; ++i) begin
          @(posedge scl);
          if (msb_lsb) begin
            data_received_slave[7-i] = sda;
          end else begin
            data_received_slave[i] = sda;
          end
        end
      end else begin                        // Si es una lectura
        for (int i=0; i<8; ++i) begin
          if (msb_lsb) begin
            if(data_sended_slave[7-i])
              force sda = 1;
            else
              force sda = 0;
          end else begin
            if(data_sended_slave[i])
              force sda = 1;
            else
              force sda = 0;
          end
          @(negedge scl);
        end
        @(negedge scl);
      end
      release sda;
  
      // ACK
      @(negedge scl);
      #1000;
      force sda  = 1'b0;
      @(negedge scl);
      release sda;

      // STop CONDITION
      @(negedge sda iff scl); 
    end
  end

endmodule
