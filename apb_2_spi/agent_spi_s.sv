`timescale 1us/1ns

// Definición del interface SPI
interface spi_if;
    logic miso;
    logic mosi;
    logic scl;
    logic cs;
endinterface

module spi_checker#(
    parameter CLK_FREC = 100000000,
    parameter SCL_FREC = 1000000
)(
    spi_if              spi, 
    input  logic        send,
    input  logic        clk,
    input  logic        arstn
);

    localparam SCL_TIME = (CLK_FREC/SCL_FREC);
    
    // -------------------------------------------------------------------
    // Propiedades de verificación (aserciones SVA)
    // -------------------------------------------------------------------
    
    // 1. SCL debe togglear sólo cuando CS es 0.
    property scl_if_cs_0;
        @(posedge clk) disable iff (!arstn)
            ($rose(spi.scl) || $fell(spi.scl)) |-> (spi.cs == 0);
    endproperty

    // 2. Luego de que CS cae (flanco de bajada) se espera que SCL se mantenga estable 
    // durante SCL_TIME ciclos.
    property cs_0_scl_stable;
        @(posedge clk) disable iff (!arstn)
            ($fell(spi.cs)) |=> $stable(spi.scl)[*(SCL_TIME-10)];
    endproperty

    // 3. Cuando CS está en 1, SCL debe estar en 1.
    property cs_1_scl_1;
        @(posedge clk) disable iff (!arstn)
            spi.cs |-> spi.scl;
    endproperty

    // 4. Cuando CS está en 1, MOSI debe estar en 1.
    property cs_1_mosi_0;
        @(posedge clk) disable iff (!arstn)
            spi.cs |-> ~spi.mosi;
    endproperty

    // 5. En el flanco de subida de SCL, MOSI debe mantenerse estable.
    property mosi_stable_at_rising;
        @(posedge clk) disable iff (!arstn)
            ($rose(spi.scl)) |-> $stable(spi.mosi);
    endproperty

    // 6. El ancho de pulso de CS: luego del flanco de bajada de CS, se espera que
    // CS vuelva a 1 (flanco de subida) entre SCL_TIME*10 y tiempo indefinido.
    property cs_pulse_width;
        @(posedge clk) disable iff (!arstn)
            ($fell(spi.cs)) |-> ##[SCL_TIME*10:$] $rose(spi.cs);
    endproperty

    // 7. SCL period
    property scl_half_period_falling_to_rising;
        @(posedge clk) disable iff (!arstn)
        $fell(spi.scl) |-> ##[SCL_TIME/2-1:SCL_TIME/2+1] $rose(spi.scl);
    endproperty

    // 8. stable mosi if not send
    property stable_mosi;
        @(posedge clk) disable iff (!arstn)
            (send == 0) |-> (spi.mosi == 0);
    endproperty

    // -------------------------------------------------------------------
    // Instanciación de las aserciones (assert property) con mensajes de error.
    // Estas se evaluarán de forma continua.
    // -------------------------------------------------------------------
    
    // 1. Verifica que SCL toggle sólo cuando CS es 0.
    assert property (scl_if_cs_0)
      else $error("ERROR: SCL toggled when CS is not 0.");

    // 2. Verifica que, luego del flanco de bajada de CS, SCL permanezca estable por SCL_TIME ciclos.
    assert property (cs_0_scl_stable)
      else $error("ERROR: SCL did not remain stable for the required time after CS fell.");

    // 3. Verifica que, cuando CS es 1, SCL esté en 1.
    assert property (cs_1_scl_1)
      else $error("ERROR: When CS is high, SCL is not high.");

    // 4. Verifica que, cuando CS es 1, MOSI esté en 1.
    assert property (cs_1_mosi_0)
      else $error("ERROR: When CS is high, MOSI is not low.");

    // 5. Verifica que MOSI se mantenga estable en el flanco de subida de SCL.
    assert property (mosi_stable_at_rising)
      else $error("ERROR: MOSI is not stable at the rising edge of SCL.");

    // 6. Verifica que el ancho de pulso de CS se encuentre dentro del rango esperado.
    assert property (cs_pulse_width)
      else $error("ERROR: CS pulse width is not within the expected range.");

    // 7. Verifica que el tiempo entre flancos de subida y bajada de SCL sea SCL_TIME/2 ciclos.
    assert property (scl_half_period_falling_to_rising)
        else $error("ERROR: El tiempo entre el flanco de bajada y el de subida de SCL no es SCL_TIME/2 ciclos.");

    // 8. Verifica que MOSI se mantenga estable si no se está enviando.
    assert property (stable_mosi)
        else $error("ERROR: MOSI is not stable if not sending.");

endmodule


class agent_spi #(parameter int N_RECEPTIONS = 256);
    // Declaramos un virtual interface del tipo spi_if
    virtual spi_if spi_vif;
    logic msb_lsb;

    // Arreglo para almacenar bytes leídos
    logic [7:0] bytes_readed[N_RECEPTIONS-1:0];
    int n_bytes_readed = 0;

    // Constructor que recibe el virtual interface y el baudrate
    function new(virtual spi_if spi_vif, logic msb_lsb);
        this.spi_vif = spi_vif;
        spi_vif.miso = 0;
    endfunction

    task automatic recive_data(ref logic enable);
        var logic [7:0] received_byte;
        wait(spi_vif.cs == 0 && enable);
        for (int i=0; i<8; ++i) begin
            @(posedge spi_vif.scl);
            if (msb_lsb)
            received_byte[7 - i] = spi_vif.mosi;
            else
                received_byte[i] = spi_vif.mosi;
            end
        if (enable) begin
            bytes_readed[n_bytes_readed] = received_byte;
            n_bytes_readed++;
        end

    endtask

    task send_data(logic [7:0] byte_to_send);
        wait(spi_vif.cs == 0);
        for (int i=0; i<8; ++i) begin
            @(negedge spi_vif.scl);
            if (msb_lsb)
                spi_vif.miso = byte_to_send[7 - i];
            else
                spi_vif.miso = byte_to_send[i];
        end
    endtask

    task set_msb_lsb(logic msb_lsb);
        this.msb_lsb = msb_lsb;
    endtask

    task reset_cnt_bytes();
        this.n_bytes_readed = 0;
    endtask


    // Tarea para validar los bytes recibidos
    task validate_received_bytes(logic [7:0] bytes_expected[N_RECEPTIONS-1:0], int num_bytes_expected);
        $display("Num bytes readed by the slave %d", n_bytes_readed);

        assert (num_bytes_expected == n_bytes_readed)
            else $error("Num bytes readed by the slave %d != %d than expected", n_bytes_readed, num_bytes_expected);

        for (int n_bytes = 0; n_bytes < n_bytes_readed; ++n_bytes) begin
            assert (bytes_expected[n_bytes] == bytes_readed[n_bytes])
                else begin
                    $error("Error los datos enviados y leidos no cuadran %d, %d", 
                        bytes_expected[n_bytes], bytes_readed[n_bytes]);
                    $stop;
                end
        end
    endtask

endclass