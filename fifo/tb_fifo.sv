`timescale 1ns/1ps

module tb_fifo;

  // Parámetros del DUT
  parameter WIDTH = 32;
  parameter DEPTH = 16; // potencia de 2

  // Señales del testbench
  logic clk;
  logic arstn;
  logic [WIDTH-1:0] data_in;
  logic [WIDTH-1:0] data_out;
  logic read;
  logic write;
  logic empty;
  logic almost_empty;
  logic full;
  logic almost_full;

  logic[WIDTH-1:0] data_send[DEPTH-1:0];
  logic[WIDTH-1:0] data_read[DEPTH-1:0];


  // Instanciación del DUT
  fifo #(
    .WIDTH(WIDTH),
    .DEPTH(DEPTH)
  ) dut (
    .clk(clk),
    .arstn(arstn),
    .data_in(data_in),
    .data_out(data_out),
    .read(read),
    .write(write),
    .empty(empty),
    .almost_empty(almost_empty),
    .full(full),
    .almost_full(almost_full)
  );

  // Generación de reloj: período de 10 ns
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  function void generate_data(integer seed, logic mode);
    begin 
      for (int i=0; i<DEPTH; ++i) begin
        if (mode) begin
          data_send[i] = i+seed;
        end else begin
          data_send[i] = $urandom(i+seed);
        end
      end
    end
  endfunction 

  task check_integrity();
    begin 
      for (int i=0; i<DEPTH; ++i) begin
        assert(data_read[i] == data_send[i]) else $error("Error los datos enviados y leidos no cuadran %d, %d", data_read[i], data_send[i]);
      end
    end
  endtask 

  task basic_test(integer seed);
    $display("[Test] Test basico.");
    generate_data(seed, 1);
    write = 1;
    for (int i=0; i<DEPTH; ++i) begin
      data_in = data_send[i];
      @(posedge clk);
    end
    write = 0;

    @(posedge clk);

    read = 1;
    for (int i=0; i<DEPTH; ++i) begin
      @(posedge clk);
      data_read[i] = data_out;
    end
    read = 0;
    check_integrity();

    @(posedge clk);
    $display("[Test PASSED] Test basico.");
  endtask 

  task test_flags();
    $display("[Test] Verificación de flags.");
    assert(empty && !full) else $error("No se empieza con la fifo a empty");
    generate_data(20, 1);
    write = 1;
    for (int i=0; i<DEPTH; ++i) @(posedge clk) data_in = data_send[i];
    write = 0;
    @(posedge clk);
    assert(full && almost_full==0) else $error("No se detecta full");

    read = 1;
    for (int i=0; i<DEPTH; ++i) @(posedge clk);
    read = 0;
    @(posedge clk);
    assert(empty && almost_empty==0) else $error("No se detecta empty");
    $display("[Test PASSED] Flags correctos.");
  endtask  

  task test_overflow_underflow();
    $display("[Test] Overflow y Underflow.");
    // llenar la fifo
    generate_data(0, 1);
    write = 1;
    for (int i=0; i<DEPTH; ++i) begin
        data_in = data_send[i];
        @(posedge clk);
    end
    @(posedge clk);
    assert(full) else $error("Full no funciona de forma correcta 1");

    // Intentar overflow
    for (int i=0; i<DEPTH; ++i) begin
      @(posedge clk); data_in=32'hFFFF; @(posedge clk);
      assert(full) else $error("Full no funciona de forma correcta 2");
    end
    
    // Vaciar FIFO
    write=0; read=1;
    read = 1;
    for (int i=0; i<DEPTH; ++i) begin
      @(posedge clk);
      data_read[i] = data_out;
    end
    read = 0;
    // Check memory protection
    check_integrity();
    @(posedge clk);
    assert(empty) else $error("Empty no funciona de forma correcta 1");

    // Intentar underflow
    for (int i=0; i<DEPTH; ++i) begin
      @(posedge clk); read=1; @(posedge clk);
      assert(empty) else $error("Empty no funciona de forma correcta 2");
      assert (data_out == 0) else $error("Assertion protection leer empty failed!");
    end
    $display("[Test PASSED] Verificación de flags y overflow/underflow.");
  endtask

  task back_to_back_rw();
    $display("[Test] Lectura/escritura simultánea.");
    write = 1; read = 0;
    for(int i=0;i<10*DEPTH;i++)begin
        data_in=i+1;
        @(posedge clk);
        if (i==DEPTH-2) read = 1;
        if(i>=DEPTH-1 && i<10*DEPTH-1 )begin
          assert (data_out == i-DEPTH+2) else $error("Assertion 1 RW dato leido %d dato enviado %d failed!", data_out, i-DEPTH+2);
        end
        if (i == 9*DEPTH-1) begin
          write = 0;
        end
    end
    read=0;
    $display("[Test PASSED] Lectura/escritura simultánea.");
  endtask

  initial begin
    arstn = 0;
    data_in = 0;
    read = 0;
    write = 0;
    @(posedge clk);
    arstn = 1;
    @(posedge clk);

    $display("Comienzo banco de test");
    basic_test(0);
    basic_test(2);
    test_flags();
    test_overflow_underflow();
    back_to_back_rw();
    $display("Fin banco de test");
    
    $stop;
  end

endmodule
