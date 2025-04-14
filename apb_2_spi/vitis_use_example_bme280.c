#include <stdio.h>
#include <stdint.h>
#include <math.h>       // Para powf() al calcular altitud
#include "platform.h"
#include "xil_printf.h"
#include "sleep.h"

//----------------------------------------------------------------------
// Definiciones de registros para tu IP SPI
// (Verifica que los offsets sean los correctos para tu diseño)
#define ADDR_SPI            0x43C00000
#define ADDR_READ_TX_STATUS 0
#define ADDR_WRITE_TX       0
#define ADDR_READ_RX_STATUS 4
#define ADDR_READ_RX_DATA   8
#define ADDR_WRITE_N_READS  12

#define REG32(addr, offset) ((volatile uint32_t *)((uintptr_t)(addr) + (offset)))
#define END_RX 0x10

//----------------------------------------------------------------------
// Estructura para la interfaz SPI
struct st_spi {
    volatile uint32_t *tx;
    volatile uint32_t *tx_status;
    volatile uint32_t *rx_status;
    volatile uint32_t *rx;
    volatile uint32_t *rx_num;
};

struct st_spi spi = {
    .tx        = REG32(ADDR_SPI, ADDR_READ_TX_STATUS),
    .tx_status = REG32(ADDR_SPI, ADDR_WRITE_TX),
    .rx_status = REG32(ADDR_SPI, ADDR_READ_RX_STATUS),
    .rx        = REG32(ADDR_SPI, ADDR_READ_RX_DATA),
    .rx_num    = REG32(ADDR_SPI, ADDR_WRITE_N_READS),
};

//----------------------------------------------------------------------
// Función de transferencia SPI: envía n_send bytes y recibe n_recv bytes.
// Se asume que la transferencia máxima es de 16 bytes por operación.
void send_recive_spi_data(int n_send, uint8_t *data_send,
                          int n_recv, uint8_t *data_recv) {
    int i;
    *spi.rx_num = n_recv;    // Especifica el número de bytes a recibir
    for (i = 0; i < n_send; i++) {
        *spi.tx = data_send[i];  // Envía cada byte
    }
    // Espera (polling) hasta que se complete la recepción
    while (!(*spi.rx_status & END_RX));
    for (i = 0; i < n_recv; i++) {
        data_recv[i] = *spi.rx;  // Lee cada byte recibido
    }
}

//----------------------------------------------------------------------
// Estructura de parámetros de calibración para Temperatura, Presión y Humedad
typedef struct {
    // Calibración de temperatura (0x88 - 0x8D, 6 bytes)
    uint16_t dig_T1;
    int16_t  dig_T2;
    int16_t  dig_T3;
    // Calibración de presión (0x8E - 0x9F, 18 bytes)
    uint16_t dig_P1;
    int16_t  dig_P2;
    int16_t  dig_P3;
    int16_t  dig_P4;
    int16_t  dig_P5;
    int16_t  dig_P6;
    int16_t  dig_P7;
    int16_t  dig_P8;
    int16_t  dig_P9;
    // Calibración de humedad
    uint8_t  dig_H1;   // Registro 0xA1
    int16_t  dig_H2;   // Registros 0xE1-0xE2
    uint8_t  dig_H3;   // Registro 0xE3
    int16_t  dig_H4;   // (0xE4 y 0xE5: (E4<<4)|(E5&0x0F))
    int16_t  dig_H5;   // (0xE5 y 0xE6: (E6<<4)|(E5>>4))
    int8_t   dig_H6;   // Registro 0xE7
} calib_data_t;

calib_data_t cal;
int32_t t_fine;  // Variable global necesaria para compensar presión y humedad

//----------------------------------------------------------------------
// Funciones para leer los registros de calibración en bloques (cumpliendo el límite de 16 bytes)
//----------------------------------------------------------------------

// 1. Lectura de los parámetros de temperatura: Registros 0x88 - 0x8D (6 bytes)
void read_temp_calib() {
    uint8_t data[6];
    uint8_t reg = 0x88 | 0x80; // Activar bit de lectura
    send_recive_spi_data(1, &reg, 6, data);
    cal.dig_T1 = (uint16_t)data[0] | ((uint16_t)data[1] << 8);
    cal.dig_T2 = (int16_t)(data[2] | ((int16_t)data[3] << 8));
    cal.dig_T3 = (int16_t)(data[4] | ((int16_t)data[5] << 8));
}

// 2. Lectura de los parámetros de presión: Registros 0x8E - 0x9F (18 bytes)
// Debido a la limitación, dividimos la lectura:
//   - Primer bloque: 16 bytes (de 0x8E a 0x9D)
//   - Segundo bloque: 2 bytes (0x9E - 0x9F)
void read_pressure_calib() {
    uint8_t data[18];
    uint8_t reg = 0x8E | 0x80;
    // Primer bloque: 16 bytes
    send_recive_spi_data(1, &reg, 16, data);
    // Segundo bloque: 2 bytes, iniciando en 0x9E
    uint8_t reg2 = 0x9E | 0x80;
    send_recive_spi_data(1, &reg2, 2, data + 16);

    cal.dig_P1 = (uint16_t)data[0]  | ((uint16_t)data[1]  << 8);
    cal.dig_P2 = (int16_t)(data[2]  | ((int16_t)data[3]  << 8));
    cal.dig_P3 = (int16_t)(data[4]  | ((int16_t)data[5]  << 8));
    cal.dig_P4 = (int16_t)(data[6]  | ((int16_t)data[7]  << 8));
    cal.dig_P5 = (int16_t)(data[8]  | ((int16_t)data[9]  << 8));
    cal.dig_P6 = (int16_t)(data[10] | ((int16_t)data[11] << 8));
    cal.dig_P7 = (int16_t)(data[12] | ((int16_t)data[13] << 8));
    cal.dig_P8 = (int16_t)(data[14] | ((int16_t)data[15] << 8));
    cal.dig_P9 = (int16_t)(data[16] | ((int16_t)data[17] << 8));
}

// 3. Lectura de los parámetros de humedad:
//    - Primero: Registro 0xA1 (1 byte)
//    - Luego: Registros 0xE1 - 0xE7 (7 bytes)
void read_humidity_calib() {
    uint8_t reg;
    // Leer H1 (0xA1)
    reg = 0xA1 | 0x80;
    send_recive_spi_data(1, &reg, 1, (uint8_t *)&cal.dig_H1);

    // Leer H2 a H6 (7 bytes, desde 0xE1)
    uint8_t data[7];
    reg = 0xE1 | 0x80;
    send_recive_spi_data(1, &reg, 7, data);
    cal.dig_H2 = (int16_t)(data[0] | ((int16_t)data[1] << 8));
    cal.dig_H3 = data[2];
    // dig_H4: (0xE4 << 4) | (0xE5 & 0x0F)
    cal.dig_H4 = (int16_t)((data[3] << 4) | (data[4] & 0x0F));
    // dig_H5: (0xE6 << 4) | ((0xE5 >> 4) & 0x0F)
    cal.dig_H5 = (int16_t)((data[5] << 4) | (data[4] >> 4));
    cal.dig_H6 = (int8_t)data[6];
}

// Función que realiza la lectura completa de todos los parámetros de calibración
void read_calibration() {
    read_temp_calib();
    read_pressure_calib();
    read_humidity_calib();
}

//----------------------------------------------------------------------
// Función para configurar el sensor (activar T, P y H)
// NOTA: Para escribir en SPI se envía la dirección con MSB = 0.
//       Por ello, en 0xF2 se envía 0xF2 & 0x7F = 0xF2 con bit 7 = 0 (0x72);
//       y en 0xF4 se envía 0xF4 & 0x7F = 0x74.
void configure_sensor() {
    uint8_t data[2];
    // Configurar humedad (registro 0xF2): oversampling x1
    data[0] = 0xF2 & 0x7F;   // 0xF2 con bit 7 = 0 → 0x72
    data[1] = 0x01;          // oversampling x1 para humedad
    send_recive_spi_data(2, data, 0, NULL);

    // Configurar temperatura y presión (registro 0xF4): oversampling x1, modo normal
    data[0] = 0xF4 & 0x7F;   // 0x74
    data[1] = 0x27;          // oversampling x1 para T y P + modo normal (bits de modo = "11")
    send_recive_spi_data(2, data, 0, NULL);
}

//----------------------------------------------------------------------
// Funciones para leer los datos "raw" de T, P y H
int32_t read_raw_temperature() {
    uint8_t data[3];
    uint8_t reg = 0xFA;  // Registro MSB de la temperatura (ya indica lectura)
    send_recive_spi_data(1, &reg, 3, data);
    int32_t adc_T = ((int32_t)data[0] << 12) |
                    ((int32_t)data[1] << 4)  |
                    ((int32_t)data[2] >> 4);
    return adc_T;
}

int32_t read_raw_pressure() {
    uint8_t data[3];
    uint8_t reg = 0xF7;  // Registro MSB de la presión
    send_recive_spi_data(1, &reg, 3, data);
    int32_t adc_P = ((int32_t)data[0] << 12) |
                    ((int32_t)data[1] << 4)  |
                    ((int32_t)data[2] >> 4);
    return adc_P;
}

int32_t read_raw_humidity() {
    uint8_t data[2];
    uint8_t reg = 0xFD;  // Registro MSB de la humedad
    send_recive_spi_data(1, &reg, 2, data);
    int32_t adc_H = ((int32_t)data[0] << 8) |
                    ((int32_t)data[1]);
    return adc_H;
}

//----------------------------------------------------------------------
// Funciones de compensación (según datasheet del BME280)
// Los resultados se obtienen en unidades de:
//   - Temperatura: 0.01 °C
//   - Presión: Pascales (Pa)
//   - Humedad: 0.001 %RH
int32_t compensate_temperature(int32_t adc_T) {
    int32_t var1, var2, T;
    var1 = ((((adc_T >> 3) - ((int32_t)cal.dig_T1 << 1))) * ((int32_t)cal.dig_T2)) >> 11;
    var2 = (((((adc_T >> 4) - ((int32_t)cal.dig_T1)) *
              ((adc_T >> 4) - ((int32_t)cal.dig_T1))) >> 12) *
              ((int32_t)cal.dig_T3)) >> 14;
    t_fine = var1 + var2;
    T = (t_fine * 5 + 128) >> 8;
    return T;
}

uint32_t compensate_pressure(int32_t adc_P) {
    int32_t var1, var2;
    uint32_t p;
    var1 = (((int32_t)t_fine) >> 1) - 64000;
    var2 = (((var1 >> 2) * (var1 >> 2)) >> 11) * cal.dig_P6;
    var2 = var2 + ((var1 * cal.dig_P5) << 1);
    var2 = (var2 >> 2) + ((int32_t)cal.dig_P4 << 16);
    var1 = (((cal.dig_P3 * (((var1 >> 2) * (var1 >> 2)) >> 13)) >> 3) +
           (((int32_t)cal.dig_P2 * var1) >> 1)) >> 18;
    var1 = ((32768 + var1) * cal.dig_P1) >> 15;
    if (var1 == 0)
        return 0;  // Evitar división por cero
    p = (((uint32_t)(1048576 - adc_P)) - (var2 >> 12)) * 3125;
    if (p < 0x80000000)
        p = (p << 1) / (uint32_t)var1;
    else
        p = (p / (uint32_t)var1) * 2;
    var1 = (((int32_t)cal.dig_P9) * ((int32_t)(((p >> 3) * (p >> 3)) >> 13))) >> 12;
    var2 = (((int32_t)(p >> 2)) * cal.dig_P8) >> 13;
    p = (uint32_t)((int32_t)p + ((var1 + var2 + cal.dig_P7) >> 4));
    return p;
}

uint32_t compensate_humidity(int32_t adc_H) {
    int32_t v_x1_u32r;
    v_x1_u32r = t_fine - ((int32_t)76800);
    v_x1_u32r = (((((adc_H << 14) - (((int32_t)cal.dig_H4) << 20) -
                   (((int32_t)cal.dig_H5) * v_x1_u32r)) + ((int32_t)16384)) >> 15) *
                 (((((((v_x1_u32r * ((int32_t)cal.dig_H6)) >> 10) *
                      (((v_x1_u32r * ((int32_t)cal.dig_H3)) >> 11) + ((int32_t)32768))) >> 10) +
                    ((int32_t)2097152)) * ((int32_t)cal.dig_H2) + 8192) >> 14));
    v_x1_u32r = v_x1_u32r - (((((v_x1_u32r >> 15) * (v_x1_u32r >> 15)) >> 7) *
                              ((int32_t)cal.dig_H1)) >> 4);
    if (v_x1_u32r < 0)
        v_x1_u32r = 0;
    if (v_x1_u32r > 419430400)
        v_x1_u32r = 419430400;
    return (uint32_t)(v_x1_u32r >> 12);
}

//----------------------------------------------------------------------
// Función principal
int main() {
    uint8_t chip_id_reg = 0xD0 | 0x80;  // Registro del chip ID (lectura)
    uint8_t chip_id;
    send_recive_spi_data(1, &chip_id_reg, 1, &chip_id);
    xil_printf("Chip ID: 0x%02X\n\r", chip_id);

    // Leer los parámetros de calibración (en bloques de acuerdo a la restricción de 16 bytes)
    read_calibration();
    xil_printf("Parámetros de calibración leídos.\n\r");

    // Configurar el sensor para mediciones de T, P y H
    configure_sensor();


    while(1){
        sleep_A9(1);
		// Leer los valores "raw" de temperatura, presión y humedad
		int32_t adc_T = read_raw_temperature();
		int32_t adc_P = read_raw_pressure();
		int32_t adc_H = read_raw_humidity();

		// Aplicar la compensación
		int32_t temp = compensate_temperature(adc_T);       // Resultado en 0.01 °C
		uint32_t pres = compensate_pressure(adc_P);           // En Pascales (Pa)
		uint32_t hum  = compensate_humidity(adc_H);            // En 0.001 %RH

		xil_printf("Temperatura Raw: %d, Compensada: %d (0.01°C)\n\r", adc_T, temp);
		xil_printf("Presión Raw: %d, Compensada: %d Pa\n\r", adc_P, pres);
		xil_printf("Humedad Raw: %d, Compensada: %d (0.001%% RH)\n\r", adc_H, hum);
		xil_printf("Medidas: %d.%02d °C, %d Pa, %d.%03d %%RH\n\r",
				   temp / 100, temp % 100, pres, hum / 1000, hum % 1000);

		float altitude = 44330.0f * (1.0f - powf((float)pres / 101325.0f, 0.1903f));
		int32_t intPart = (int32_t)altitude;
		int32_t fracPart = (int32_t)((altitude - intPart) * 100);

		if (fracPart < 0)
			fracPart = -fracPart;

		xil_printf("Altitud estimada: %d.%02d m\n\r", intPart, fracPart);
    }
    cleanup_platform();
    return 0;
}
