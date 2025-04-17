`timescale 1ns/1ps
`include "agent_i2c.sv"

module tb_i2c;

  // Parámetros del testbench
  localparam CLK_FREQ    = 100_000_000;  // 100 MHz
  localparam I2C_FREQ    = 100_000;      // 100 KHz
  localparam CLK_PERIOD  = 10;           // Período reloj 100 MHz
  localparam N_RECEPTIONS= 256;          // Número de recepciones

  // Señales internas del testbench
  logic clk;
  logic arstn;
  logic [7:0] byte_2_send;
  logic [7:0] byte_received;
  logic ena_i2c;
  logic end_trans;
  logic msb_lsb;
  logic [7:0] adrr_r_w;

  logic[7:0] data_sended[N_RECEPTIONS-1:0];
  logic[7:0] data_received[N_RECEPTIONS-1:0];
  integer n_bytes_received = 0;
  integer n_bytes_sended = 0;

  // Interfaz I²C
  i2c_if i2c_vif();

  // Pull-up virtual sobre la señal SDA
  pullup(i2c_vif.sda);

  // Clase Agent I²C (slave virtual)
  agent_i2c #(N_RECEPTIONS,
              6'h34) agent_i2c_h;

  // DUT (Master)
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
      .sda(i2c_vif.sda),
      .scl(i2c_vif.scl)
  );

  i2c_checker checker_ins(
    .i2c_vif(i2c_vif),
    .clk(clk),
    .arstn(arstn)
  );

    // Tarea para validar los bytes recibidos
  task validate_received_bytes();
    for (int n_bytes = 0; n_bytes < N_RECEPTIONS; ++n_bytes) begin
        assert (data_sended[n_bytes] == data_received[n_bytes])
            else begin
                $error("Error los datos enviados y leidos no cuadran %d, %d", 
                              data_sended[n_bytes], data_received[n_bytes]);
                $stop;
            end
    end
  endtask

  // Tareas para control del Master
  task automatic read_bytes_master(int n_bytes,ref logic [7:0] data[N_RECEPTIONS-1:0], logic [6:0] addr);
    ena_i2c = 1;
    adrr_r_w = {addr, 1'b1};
    byte_2_send = 8'h00;
    repeat(1) @(posedge end_trans);
    for (int i=0; i<n_bytes; ++i) begin
      repeat(1) @(posedge end_trans);
      data[n_bytes_received] = byte_received;
      n_bytes_received++;
    end
    #1000 @(posedge clk);
    ena_i2c = 0;
    @(negedge end_trans);
    #1000 @(posedge clk);
  endtask

  task automatic send_bytes_master(int n_bytes,logic [7:0] data[N_RECEPTIONS-1:0], logic [6:0] addr);
    ena_i2c = 1;
    adrr_r_w = {addr, 1'b0};
    byte_2_send = data[n_bytes_sended];
    repeat(1) @(posedge end_trans);
    for (int i=0; i<n_bytes; ++i) begin      
      byte_2_send = data[n_bytes_sended];
      repeat(1) @(posedge end_trans);
      n_bytes_sended++;
    end
    #1000 @(posedge clk);
    ena_i2c = 0;
    @(negedge end_trans);
    #1000 @(posedge clk);
  endtask

  function void generate_data(integer seed, logic mode);
    begin 
        for (int i=0; i<N_RECEPTIONS; ++i) begin
            if (mode) begin
                data_sended[i] = i+seed;
            end else begin
                data_sended[i] = $urandom(i+seed);
            end
        end
    end
  endfunction 

  // Generación del reloj (clk)
  initial begin
    clk = 0;
    forever #(CLK_PERIOD/2) clk = ~clk;
  end

  // Inicialización de señales y reset
  initial begin
    ena_i2c     = 0;
    msb_lsb     = 1;            // MSB primero
    adrr_r_w    = 8'h00;        
    byte_2_send = 8'h00;        
    arstn       = 0;

    generate_data(0, 1);
    agent_i2c_h = new(i2c_vif, data_sended);

    #20 @(posedge clk);
    arstn = 1;
  end

  // Hilo separado para la ejecución del agente (slave)
  initial begin
    @(posedge arstn);
    forever begin
      agent_i2c_h.i2c_slave_handle_frame();
    end
  end

  // Secuencia principal del test
  initial begin
    logic [6:0] addr_slave = 7'h34;
    int n_bytes;
    int i;

    @(posedge arstn);
    #20 @(posedge clk);

    n_bytes = $urandom_range(1, 10);
    for (i=0; i<N_RECEPTIONS-10; i+=n_bytes) begin
      n_bytes = $urandom_range(1, 10);
      // Enviar byte al slave (desde el master)
      send_bytes_master(n_bytes, data_sended, addr_slave);
      #40000;  
    end
    send_bytes_master(N_RECEPTIONS-i, data_sended, addr_slave);
    #40000;  

    n_bytes = $urandom_range(1, 10);
    for (i=0; i<N_RECEPTIONS-10; i+=n_bytes) begin
      n_bytes = $urandom_range(1, 10);
      // Leer byte desde el slave (desde el master)
      read_bytes_master(n_bytes, data_received, addr_slave);
      #40000;  
    end
    read_bytes_master(N_RECEPTIONS-i, data_received, addr_slave);
    #40000;

    // Validar los bytes recibidos
    validate_received_bytes();

    // Finaliza la simulación tras tiempo extra para observación
    #40000;
    $finish;
  end

endmodule
