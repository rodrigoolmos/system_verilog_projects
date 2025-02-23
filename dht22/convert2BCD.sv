
module convert2BCD(
    input logic [15:0] numero,
    output logic negativo,
    output logic [3:0] decenas,
    output logic [3:0] unidades,
    output logic [3:0] decimal
);
    
    logic [28:0] entero;
    /* ----- magic number division ------- */
    // Utilizamos el metod0 de multiplicación por el inverso: para dividir entre 10 
    // (numero * 6554) >> 16 equivale a numero / 10 para números de 16 bits
    // El resto se obtiene restando: numero - (cociente * 10)

    always_comb begin
        entero = (numero[14:0] * 16'd6554) >> 16;
        decimal = numero[14:0] - (entero * 10);
        decenas = (entero * 16'd6554) >> 16;
        unidades = entero - (decenas * 10);
        negativo = numero[15];
    end


endmodule