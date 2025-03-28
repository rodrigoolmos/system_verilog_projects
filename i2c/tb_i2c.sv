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

  logic [7:0] data_received_master;


  typedef enum logic[2:0] {idle, addr_r_w, ack, send_byte_st, receive_byte_st} state_i2c_t;
  state_i2c_t state_i2c_slave;

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

  task automatic read_byte_slave(ref logic [7:0] data);
    for (int i=0; i<8; ++i) begin
      @(posedge scl);
      if (msb_lsb) begin
        data[7-i] = sda;
      end else begin
        data[i] = sda;
      end
    end
    @(negedge scl);
  endtask


  task automatic send_byte_slave(ref logic [7:0] data);
    #4000;
    wait(scl == 0);
    for (int i=0; i<8; ++i) begin
      if (msb_lsb) begin
        if(data[7-i])
          force sda = 1;
        else
          force sda = 0;
      end else begin
        if(data[i])
          force sda = 1;
        else
          force sda = 0;
      end
      @(negedge scl);
    end
  endtask

  task gen_ack();
    #2000;
    force sda  = 1'b0;
    @(posedge scl);
    #4000;
    release sda;
  endtask

  task automatic read_byte_master(ref logic [7:0] data, logic [6:0] addr);
    ena_i2c = 1;
    adrr_r_w   = {addr, 1'b1};
    byte_2_send = 8'h00;
    repeat(2) @(posedge end_trans);
    #1000 @(posedge clk);
    ena_i2c = 0;
    data = byte_received;
    @(negedge end_trans);
    #1000@(posedge clk);
  endtask

  task send_byte_master(logic [7:0] data, logic [6:0] addr);
    ena_i2c = 1;
    adrr_r_w   = {addr, 1'b0};
    byte_2_send = data;
    repeat(2) @(posedge end_trans);  
    #1000 @(posedge clk);
    ena_i2c = 0;
    @(negedge end_trans);
    #1000@(posedge clk);
  endtask

  // Generación de reloj
  initial begin
    clk = 0;
    forever #(CLK_PERIOD/2) clk = ~clk;
  end

  // Generación de reset e Inicialización de señales
  initial begin
    ena_i2c     = 0;
    msb_lsb     = 1;            // Suponiendo que '1' es MSB primero
    adrr_r_w    = 8'h00;        // Ejemplo de dirección (7-bit + bit W)
    byte_2_send = 8'h00;        // Ejemplo de byte a enviar
    arstn = 0;
    #20 @(posedge clk);         // Mantener el reset por 20 ns
    arstn = 1;
  end

  // Estímulo inicial
  initial begin
    logic [6:0] addr_slave;
    // Esperar al final del reset
    @(posedge arstn);
    #20 @(posedge clk);

    addr_slave = 7'h34;
    send_byte_master(8'h34, addr_slave);
    read_byte_master(data_received_master, addr_slave);

    // Finalizar simulación tras un tiempo adicional
    #40000;
    $finish;
  end


  initial begin
    data_sended_slave = 8'h29;  // Ejemplo de byte a enviar
    state_i2c_slave = idle;
    release sda;
    forever begin
      case (state_i2c_slave)
        idle: begin
          @(negedge sda iff scl);
          state_i2c_slave = addr_r_w;
        end
        addr_r_w: begin
          read_byte_slave(addres_received_slave);
          state_i2c_slave = ack;
        end
        ack: begin
          gen_ack();
          if (addres_received_slave[0])
            state_i2c_slave = send_byte_st;
          else
            state_i2c_slave = receive_byte_st;
        end
        send_byte_st: begin
          fork
            begin
              send_byte_slave(data_sended_slave);
              state_i2c_slave = ack;
            end
            begin
              @(posedge sda iff scl);
              state_i2c_slave = idle;
            end
          join_any
        end
        receive_byte_st: begin
          fork
            begin
              read_byte_slave(data_received_slave);
              state_i2c_slave = ack;
            end
            begin
              @(posedge sda iff scl);
              state_i2c_slave = idle;
            end
          join_any
        end
      endcase
    end
  end

endmodule
