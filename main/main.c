#include <string.h>
#include <sys/param.h>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/event_groups.h"
#include "esp_system.h"
#include "esp_wifi.h"
#include "esp_event.h"
#include "esp_log.h"
#include "nvs_flash.h"
#include "lwip/err.h"
#include "lwip/sockets.h"
#include "lwip/netdb.h"
#include "cJSON.h"
#include "mbedtls/sha256.h"
#include "driver/uart.h"
#include "driver/gpio.h"
#include "mbedtls/bignum.h"

#define TXD_PIN 17
#define RXD_PIN 18
#define UART_PORT UART_NUM_1

#define WIFI_SSID CONFIG_WIFI_SSID
#define WIFI_PASS CONFIG_WIFI_PASSWORD
#define BTC_ADDRESS CONFIG_BTC_ADDRESS

#define POOL_URL "pool.nerdminer.io"
#define POOL_PORT 3333
#define WORKER_NAME "MS-minis3"

static const char *TAG = "MICRO_STRATUM";

// --- VARIÁVEIS DE MEMÓRIA DO CÉREBRO ---
double g_pool_difficulty = 1.0;
uint8_t g_current_header[80] = {0};
char g_last_job_id[32] = {0};
char g_last_ntime[16] = {0};
char g_extranonce1[32] = {0};
int g_extranonce2_size = 0;

// ============================================================================
// NÚCLEO SHA-256 PURO (Para calcular o Midstate no S3)
// ============================================================================
static const uint32_t sha256_k[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

#define ROTR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))
#define CH(x, y, z) (((x) & (y)) ^ (~(x) & (z)))
#define MAJ(x, y, z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))
#define EP0(x) (ROTR(x, 2) ^ ROTR(x, 13) ^ ROTR(x, 22))
#define EP1(x) (ROTR(x, 6) ^ ROTR(x, 11) ^ ROTR(x, 25))
#define SIG0(x) (ROTR(x, 7) ^ ROTR(x, 18) ^ ((x) >> 3))
#define SIG1(x) (ROTR(x, 17) ^ ROTR(x, 19) ^ ((x) >> 10))

void sha256_transform(uint32_t *state, const uint8_t *data) {
    uint32_t a, b, c, d, e, f, g, h, i, T1, T2;
    uint32_t W[64];
    for (i = 0; i < 16; i++) W[i] = (data[i * 4] << 24) | (data[i * 4 + 1] << 16) | (data[i * 4 + 2] << 8) | data[i * 4 + 3];
    for (i = 16; i < 64; i++) W[i] = SIG1(W[i - 2]) + W[i - 7] + SIG0(W[i - 15]) + W[i - 16];
    a = state[0]; b = state[1]; c = state[2]; d = state[3];
    e = state[4]; f = state[5]; g = state[6]; h = state[7];
    for (i = 0; i < 64; i++) {
        T1 = h + EP1(e) + CH(e, f, g) + sha256_k[i] + W[i];
        T2 = EP0(a) + MAJ(a, b, c);
        h = g; g = f; f = e; e = d + T1;
        d = c; c = b; b = a; a = T1 + T2;
    }
    state[0] += a; state[1] += b; state[2] += c; state[3] += d;
    state[4] += e; state[5] += f; state[6] += g; state[7] += h;
}

static const uint32_t sha256_initial_hash[8] = {
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
};

void calculate_midstate(const uint8_t *header64, uint8_t *midstate_out) {
    uint32_t state[8];
    memcpy(state, sha256_initial_hash, 32);
    sha256_transform(state, header64);
    for(int i=0; i<8; i++) {
        midstate_out[i*4]   = (state[i] >> 24) & 0xFF;
        midstate_out[i*4+1] = (state[i] >> 16) & 0xFF;
        midstate_out[i*4+2] = (state[i] >> 8)  & 0xFF;
        midstate_out[i*4+3] = (state[i] >> 0)  & 0xFF;
    }
}

// ============================================================================
// FUNÇÕES AUXILIARES DE CRIPTOGRAFIA E REDE
// ============================================================================

uint8_t get_crc5(uint8_t *ptr, uint8_t len) {
    uint8_t i, j, crc = 0x1f;
    for (i = 0; i < len; i++) {
        crc ^= ptr[i];
        for (j = 0; j < 8; j++) {
            if (crc & 0x80) crc = (crc << 1) ^ 0x05;
            else crc <<= 1;
        }
    }
    return ((crc >> 3) & 0x1f);
}

void calculate_target(double difficulty, uint8_t *target_out) {
    memset(target_out, 0, 32);
    if (difficulty <= 0.0) difficulty = 1.0;

    mbedtls_mpi diff1, pool_diff, result;
    mbedtls_mpi_init(&diff1); mbedtls_mpi_init(&pool_diff); mbedtls_mpi_init(&result);

    mbedtls_mpi_read_string(&diff1, 16, "00000000FFFF0000000000000000000000000000000000000000000000000000");
    mbedtls_mpi_mul_int(&diff1, &diff1, 1000);
    int diff_int = (int)(difficulty * 1000);

    mbedtls_mpi_lset(&pool_diff, diff_int);
    mbedtls_mpi_div_mpi(&result, NULL, &diff1, &pool_diff);
    mbedtls_mpi_write_binary(&result, target_out, 32);

    mbedtls_mpi_free(&diff1); mbedtls_mpi_free(&pool_diff); mbedtls_mpi_free(&result);
}

void init_uart() {
    uart_config_t uart_config = {
        .baud_rate = 115200,
        .data_bits = UART_DATA_8_BITS,
        .parity = UART_PARITY_DISABLE,
        .stop_bits = UART_STOP_BITS_1,
        .flow_ctrl = UART_HW_FLOWCTRL_DISABLE,
        .source_clk = UART_SCLK_DEFAULT,
    };
    ESP_ERROR_CHECK(uart_param_config(UART_PORT, &uart_config));
    ESP_ERROR_CHECK(uart_set_pin(UART_PORT, TXD_PIN, RXD_PIN, UART_PIN_NO_CHANGE, UART_PIN_NO_CHANGE));
    ESP_ERROR_CHECK(uart_driver_install(UART_PORT, 1024, 1024, 0, NULL, 0));
    ESP_LOGI("UART", "Porta Serial inicializada nos pinos TX:%d RX:%d", TXD_PIN, RXD_PIN);
}

void test_uart_ping_pong() {
    ESP_LOGW("UART_TEST", "--- INICIANDO TESTE FÍSICO PING-PONG ---");
    ESP_LOGI("UART_TEST", "Enviando 'PING' para o C3...");
    uart_flush(UART_PORT);
    uart_write_bytes(UART_PORT, "PING", 4);

    uint8_t rx_buf[128] = {0};
    int len = uart_read_bytes(UART_PORT, rx_buf, sizeof(rx_buf) - 1, 2000 / portTICK_PERIOD_MS);

    if (len > 0) {
        rx_buf[len] = '\0';
        if (strstr((char *)rx_buf, "PONG") != NULL) {
            ESP_LOGI("UART_TEST", "SUCESSO ABSOLUTO! Recebido: %s", rx_buf);
        } else {
            ESP_LOGE("UART_TEST", "FALHA! Recebido %d bytes de 'lixo' em vez de PONG.", len);
            ESP_LOG_BUFFER_HEX("UART_TEST_HEX", rx_buf, len);
        }
    } else {
        ESP_LOGE("UART_TEST", "FALHA! Sem resposta (Timeout de 2 segundos).");
    }
    ESP_LOGW("UART_TEST", "----------------------------------------");
}

static void wifi_event_handler(void *arg, esp_event_base_t event_base, int32_t event_id, void *event_data) {
    if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_START) esp_wifi_connect();
    else if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_DISCONNECTED) {
        esp_wifi_connect();
        ESP_LOGI(TAG, "Tentando reconectar ao Wi-Fi...");
    }
    else if (event_base == IP_EVENT && event_id == IP_EVENT_STA_GOT_IP) {
        ip_event_got_ip_t *event = (ip_event_got_ip_t *)event_data;
        ESP_LOGI(TAG, "Conectado! IP recebido: " IPSTR, IP2STR(&event->ip_info.ip));
    }
}

void hex_to_bytes(const char *hex, uint8_t *bytes) {
    size_t len = strlen(hex);
    for (size_t i = 0; i < len; i += 2) sscanf(hex + i, "%02hhx", &bytes[i / 2]);
}

void double_sha256(const uint8_t *data, size_t len, uint8_t *out) {
    uint8_t hash1[32];
    mbedtls_sha256(data, len, hash1, 0);
    mbedtls_sha256(hash1, 32, out, 0);
}

void process_mining_notify(cJSON *params) {
    const char *job_id = cJSON_GetArrayItem(params, 0)->valuestring;
    const char *prev_hash_hex = cJSON_GetArrayItem(params, 1)->valuestring;
    const char *coinb1 = cJSON_GetArrayItem(params, 2)->valuestring;
    const char *coinb2 = cJSON_GetArrayItem(params, 3)->valuestring;
    cJSON *merkle_branches = cJSON_GetArrayItem(params, 4);

    ESP_LOGI("STRATUM_PARSER", "Novo Trabalho Recebido: %s", job_id);

    char extranonce2_hex[9] = "00000000";

    size_t coinb_len = strlen(coinb1) + strlen(g_extranonce1) + strlen(extranonce2_hex) + strlen(coinb2);
    char *coinbase_hex = malloc(coinb_len + 1);
    strcpy(coinbase_hex, coinb1);
    strcat(coinbase_hex, g_extranonce1);
    strcat(coinbase_hex, extranonce2_hex);
    strcat(coinbase_hex, coinb2);

    size_t coinbase_bin_len = coinb_len / 2;
    uint8_t *coinbase_bin = malloc(coinbase_bin_len);
    hex_to_bytes(coinbase_hex, coinbase_bin);

    uint8_t current_hash[32];
    double_sha256(coinbase_bin, coinbase_bin_len, current_hash);
    free(coinbase_hex); free(coinbase_bin);

    int branch_count = cJSON_GetArraySize(merkle_branches);
    uint8_t branch_bin[32], combined[64];

    for (int i = 0; i < branch_count; i++) {
        const char *branch_hex = cJSON_GetArrayItem(merkle_branches, i)->valuestring;
        hex_to_bytes(branch_hex, branch_bin);
        memcpy(combined, current_hash, 32);
        memcpy(combined + 32, branch_bin, 32);
        double_sha256(combined, 64, current_hash);
    }
    ESP_LOGI("STRATUM_PARSER", "Merkle Root calculado com sucesso! (Nível: %d)", branch_count);

    uint8_t header[80] = {0};
    const char *version_hex = cJSON_GetArrayItem(params, 5)->valuestring;
    const char *nbits_hex = cJSON_GetArrayItem(params, 6)->valuestring;
    const char *ntime_hex = cJSON_GetArrayItem(params, 7)->valuestring;

    hex_to_bytes(version_hex, &header[0]);   
    hex_to_bytes(prev_hash_hex, &header[4]); 
    memcpy(&header[36], current_hash, 32);   
    hex_to_bytes(ntime_hex, &header[68]);    
    hex_to_bytes(nbits_hex, &header[72]);    

    // CÉREBRO: Guarda os dados para comparar o Hash depois
    memcpy(g_current_header, header, 80);
    strcpy(g_last_job_id, job_id);
    strcpy(g_last_ntime, ntime_hex);

    uint8_t midstate[32] = {0};
    calculate_midstate(header, midstate);

    uint8_t asic_packet[70] = {0};
    asic_packet[0] = 0x55; 
    asic_packet[1] = 0xAA; 
    asic_packet[2] = 0x21; // SEND_WORK ORIGINAL
    asic_packet[3] = 0x42; 

    memcpy(&asic_packet[4], midstate, 32);
    memcpy(&asic_packet[36], &header[64], 12);
    asic_packet[69] = get_crc5(&asic_packet[2], 67);

    uart_write_bytes(UART_PORT, asic_packet, 70);
    ESP_LOGI("UART", "=> Pacote 0x21 de 70 bytes enviado para o ASIC!");
}

static void stratum_client_task(void *pvParameters) {
    while (1) {
        struct hostent *hp = gethostbyname(POOL_URL);
        if (!hp) {
            vTaskDelay(2000 / portTICK_PERIOD_MS);
            continue;
        }

        struct sockaddr_in dest_addr;
        inet_pton(AF_INET, inet_ntoa(*(struct in_addr *)hp->h_addr), &dest_addr.sin_addr);
        dest_addr.sin_family = AF_INET;
        dest_addr.sin_port = htons(POOL_PORT);

        int sock = socket(AF_INET, SOCK_STREAM, IPPROTO_IP);
        if (sock < 0) break;
        
        ESP_LOGI(TAG, "Conectando a %s:%d...", POOL_URL, POOL_PORT);
        if (connect(sock, (struct sockaddr *)&dest_addr, sizeof(struct sockaddr_in)) != 0) {
            close(sock);
            vTaskDelay(2000 / portTICK_PERIOD_MS);
            continue;
        }
        ESP_LOGI(TAG, "Conectado à Pool!");

        const char *subscribe_msg = "{\"id\": 1, \"method\": \"mining.subscribe\", \"params\": []}\n";
        send(sock, subscribe_msg, strlen(subscribe_msg), 0);
        
        char auth_msg[200];
        snprintf(auth_msg, sizeof(auth_msg), "{\"id\": 2, \"method\": \"mining.authorize\", \"params\": [\"%s.%s\", \"x\"]}\n", BTC_ADDRESS, WORKER_NAME);
        send(sock, auth_msg, strlen(auth_msg), 0);

        char *rx_buffer = calloc(4096, sizeof(char));
        int rx_len = 0;

        while (1) {
            // TCP de Forma Assíncrona (MSG_DONTWAIT evita que o loop trave aqui)
            int len = recv(sock, rx_buffer + rx_len, 4096 - rx_len - 1, MSG_DONTWAIT);
            if (len < 0) {
                // Se o erro não for de "tentar novamente" (EAGAIN), a rede caiu
                if (errno != EAGAIN && errno != EWOULDBLOCK && errno != 11) {
                    ESP_LOGE(TAG, "Erro na recepção TCP: errno %d", errno);
                    break;
                }
            } else if (len == 0) {
                ESP_LOGW(TAG, "Conexão fechada pela Pool.");
                break;
            } else {
                rx_len += len;
                rx_buffer[rx_len] = '\0';

                char *newline;
                while ((newline = strchr(rx_buffer, '\n')) != NULL) {
                    *newline = '\0';
                    cJSON *json = cJSON_Parse(rx_buffer);
                    if (json) {
                        cJSON *method = cJSON_GetObjectItem(json, "method");
                        if (method) {
                            if (strcmp(method->valuestring, "mining.notify") == 0) {
                                process_mining_notify(cJSON_GetObjectItem(json, "params"));
                            } else if (strcmp(method->valuestring, "mining.set_difficulty") == 0) {
                                cJSON *diff_arr = cJSON_GetObjectItem(json, "params");
                                if (cJSON_IsArray(diff_arr)) {
                                    g_pool_difficulty = cJSON_GetArrayItem(diff_arr, 0)->valuedouble;
                                    ESP_LOGW("STRATUM", "Dificuldade da Pool atualizada: %.3f", g_pool_difficulty);
                                }
                            }
                        }

                        cJSON *id = cJSON_GetObjectItem(json, "id");
                        if (id && id->valueint == 1) {
                            cJSON *result = cJSON_GetObjectItem(json, "result");
                            if (cJSON_IsArray(result)) {
                                strcpy(g_extranonce1, cJSON_GetArrayItem(result, 1)->valuestring);
                                g_extranonce2_size = cJSON_GetArrayItem(result, 2)->valueint;
                                ESP_LOGI(TAG, "Extranonce1 capturado!");
                            }
                        }
                        cJSON_Delete(json);
                    }
                    int remaining = rx_len - (newline - rx_buffer) - 1;
                    if (remaining > 0) memmove(rx_buffer, newline + 1, remaining);
                    rx_len = remaining;
                    rx_buffer[rx_len] = '\0';
                }
            }

            // --- ESCUTA ASSÍNCRONA DO C3 E JULGAMENTO DO HASH ---
            uint8_t asic_resp[32];
            int uart_len = uart_read_bytes(UART_PORT, asic_resp, 11, 10 / portTICK_PERIOD_MS);

            if (uart_len == 11 && asic_resp[0] == 0xAA && asic_resp[1] == 0x55) {
                uint32_t nonce = (asic_resp[4] << 24) | (asic_resp[5] << 16) | (asic_resp[6] << 8) | asic_resp[7];
                ESP_LOGI("CÉREBRO_S3", "Nonce recebido do ASIC: %08lx. Avaliando...", (unsigned long)nonce);

                g_current_header[76] = asic_resp[7];
                g_current_header[77] = asic_resp[6];
                g_current_header[78] = asic_resp[5];
                g_current_header[79] = asic_resp[4];

                uint8_t hash1[32], hash2[32];
                mbedtls_sha256(g_current_header, 80, hash1, 0);
                mbedtls_sha256(hash1, 32, hash2, 0);

                uint8_t target[32];
                calculate_target(g_pool_difficulty, target);

                uint8_t hash_rev[32];
                for (int i = 0; i < 32; i++) hash_rev[i] = hash2[31 - i];

                bool is_valid = false;
                for (int i = 0; i < 32; i++) {
                    if (hash_rev[i] < target[i]) { is_valid = true; break; } 
                    if (hash_rev[i] > target[i]) { is_valid = false; break; } 
                }

                if (is_valid) {
                    char nonce_hex[9];
                    sprintf(nonce_hex, "%08lx", (unsigned long)nonce);
                    ESP_LOGW("CÉREBRO_S3", "SHARE APROVADO! Enviando para a Pool...");
                    char submit_msg[256];
                    snprintf(submit_msg, sizeof(submit_msg),
                             "{\"id\": 4, \"method\": \"mining.submit\", \"params\": [\"%s.%s\", \"%s\", \"00000000\", \"%s\", \"%s\"]}\n",
                             BTC_ADDRESS, WORKER_NAME, g_last_job_id, g_last_ntime, nonce_hex);
                    send(sock, submit_msg, strlen(submit_msg), 0);
                } else {
                    ESP_LOGE("CÉREBRO_S3", "Share rejeitado pelo S3. Poupando o seu banimento!");
                }
            }

            // Respiro do sistema para o Watchdog não resetar a placa
            vTaskDelay(10 / portTICK_PERIOD_MS); 
        }
        
        free(rx_buffer);
        if (sock != -1) { shutdown(sock, 0); close(sock); }
    }
}

void app_main(void) {
    init_uart();
    test_uart_ping_pong();
    ESP_ERROR_CHECK(nvs_flash_init());
    ESP_ERROR_CHECK(esp_netif_init());
    ESP_ERROR_CHECK(esp_event_loop_create_default());
    esp_netif_create_default_wifi_sta();

    wifi_init_config_t cfg = WIFI_INIT_CONFIG_DEFAULT();
    ESP_ERROR_CHECK(esp_wifi_init(&cfg));
    ESP_ERROR_CHECK(esp_event_handler_instance_register(WIFI_EVENT, ESP_EVENT_ANY_ID, &wifi_event_handler, NULL, NULL));
    ESP_ERROR_CHECK(esp_event_handler_instance_register(IP_EVENT, IP_EVENT_STA_GOT_IP, &wifi_event_handler, NULL, NULL));

    wifi_config_t wifi_config = {
        .sta = {
            .ssid = WIFI_SSID,
            .password = WIFI_PASS,
        },
    };
    ESP_ERROR_CHECK(esp_wifi_set_mode(WIFI_MODE_STA));
    ESP_ERROR_CHECK(esp_wifi_set_config(WIFI_IF_STA, &wifi_config));
    ESP_ERROR_CHECK(esp_wifi_start());

    vTaskDelay(5000 / portTICK_PERIOD_MS);
    xTaskCreate(stratum_client_task, "stratum_task", 8192, NULL, 5, NULL);
}