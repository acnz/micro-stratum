#include <string.h>
#include <sys/param.h>
#include <math.h>
#include <stdlib.h>
#include "sdkconfig.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "esp_system.h"
#include "esp_wifi.h"
#include "esp_event.h"
#include "esp_log.h"
#include "nvs_flash.h"
#include "lwip/sockets.h"
#include "lwip/netdb.h"
#include "cJSON.h"
#include "mbedtls/sha256.h"
#include "driver/uart.h"
#include "mbedtls/bignum.h"
#include "esp_http_server.h"
#include "esp_timer.h"

// --- CONFIGURAÇÕES KCONFIG ---
#define TXD_PIN CONFIG_UART_TXD
#define RXD_PIN CONFIG_UART_RXD
#define UART_PORT UART_NUM_1

#define WIFI_SSID CONFIG_WIFI_SSID
#define WIFI_PASS CONFIG_WIFI_PASSWORD
#define BTC_ADDRESS CONFIG_BTC_ADDRESS
#define POOL_URL CONFIG_POOL_URL
#define POOL_PORT CONFIG_POOL_PORT
#define WORKER_NAME CONFIG_WORKER_NAME

static const char *TAG = "MICRO_STRATUM_GENESIS";

// --- ESTATÍSTICAS GLOBAIS ---
uint32_t g_shares_sent = 0;
uint32_t g_shares_disc = 0;
uint32_t g_shares_accepted = 0;
uint32_t g_shares_rejected = 0;
int64_t g_start_time = 0;
char g_last_accepted_times[4][64];
int g_accepted_idx = 0;

double g_pool_difficulty = 1.0;
double g_best_diff = 0.0; 
double g_network_difficulty = 1.0;
double g_network_odds = 0.0;

uint8_t g_current_header[80] = {0};
char g_last_job_id[32] = "genesis_test";
char g_last_ntime[16] = "495fab29";

char g_extranonce1[32] = {0};
int g_extranonce2_size = 4;          
char g_extranonce2[32] = "00000000"; 

// ============================================================================
// MATEMÁTICA SHA-256 (MIDSTATE)
// ============================================================================
static const uint32_t sha256_k[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};
#define ROTR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))
#define CH(x, y, z) (((x) & (y)) ^ (~(x) & (z)))
#define MAJ(x, y, z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))
#define EP0(x) (ROTR(x, 2) ^ ROTR(x, 13) ^ ROTR(x, 22))
#define EP1(x) (ROTR(x, 6) ^ ROTR(x, 11) ^ ROTR(x, 25))
#define SIG0(x) (ROTR(x, 7) ^ ROTR(x, 18) ^ ((x) >> 3))
#define SIG1(x) (ROTR(x, 17) ^ ROTR(x, 19) ^ ((x) >> 10))

void sha256_transform(uint32_t *state, const uint8_t *data)
{
    uint32_t a, b, c, d, e, f, g, h, i, T1, T2, W[64];
    for (i = 0; i < 16; i++)
        W[i] = (data[i * 4] << 24) | (data[i * 4 + 1] << 16) | (data[i * 4 + 2] << 8) | data[i * 4 + 3];
    for (i = 16; i < 64; i++)
        W[i] = SIG1(W[i - 2]) + W[i - 7] + SIG0(W[i - 15]) + W[i - 16];
    a = state[0]; b = state[1]; c = state[2]; d = state[3];
    e = state[4]; f = state[5]; g = state[6]; h = state[7];
    for (i = 0; i < 64; i++)
    {
        T1 = h + EP1(e) + CH(e, f, g) + sha256_k[i] + W[i];
        T2 = EP0(a) + MAJ(a, b, c);
        h = g; g = f; f = e; e = d + T1;
        d = c; c = b; b = a; a = T1 + T2;
    }
    state[0] += a; state[1] += b; state[2] += c; state[3] += d;
    state[4] += e; state[5] += f; state[6] += g; state[7] += h;
}

void calculate_midstate(const uint8_t *header64, uint8_t *midstate_out)
{
    uint32_t state[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
    sha256_transform(state, header64);
    for (int i = 0; i < 8; i++)
    {
        midstate_out[i * 4] = (state[i] >> 24) & 0xFF;
        midstate_out[i * 4 + 1] = (state[i] >> 16) & 0xFF;
        midstate_out[i * 4 + 2] = (state[i] >> 8) & 0xFF;
        midstate_out[i * 4 + 3] = state[i] & 0xFF;
    }
}

// ============================================================================
// FUNÇÕES AUXILIARES
// ============================================================================
uint8_t get_crc5(uint8_t *ptr, uint8_t len)
{
    uint8_t i, j, crc = 0x1f;
    for (i = 0; i < len; i++)
    {
        crc ^= ptr[i];
        for (j = 0; j < 8; j++)
        {
            if (crc & 0x80) crc = (crc << 1) ^ 0x05;
            else crc <<= 1;
        }
    }
    return ((crc >> 3) & 0x1f);
}

void hex_to_bytes(const char *hex, uint8_t *bytes)
{
    size_t len = strlen(hex);
    for (size_t i = 0; i < len / 2; i++)
    {
        char high = hex[i * 2], low = hex[i * 2 + 1];
        uint8_t h = (high >= '0' && high <= '9') ? (high - '0') : (high >= 'a' && high <= 'f') ? (high - 'a' + 10) : (high >= 'A' && high <= 'F') ? (high - 'A' + 10) : 0;
        uint8_t l = (low >= '0' && low <= '9') ? (low - '0') : (low >= 'a' && low <= 'f') ? (low - 'a' + 10) : (low >= 'A' && low <= 'F') ? (low - 'A' + 10) : 0;
        bytes[i] = (h << 4) | l;
    }
}

void double_sha256(const uint8_t *data, size_t len, uint8_t *out)
{
    uint8_t h1[32];
    mbedtls_sha256(data, len, h1, 0);
    mbedtls_sha256(h1, 32, out, 0);
}

void calculate_target(double difficulty, uint8_t *target_out)
{
    mbedtls_mpi diff1, pool_diff, result;
    mbedtls_mpi_init(&diff1); mbedtls_mpi_init(&pool_diff); mbedtls_mpi_init(&result);
    mbedtls_mpi_read_string(&diff1, 16, "00000000FFFF0000000000000000000000000000000000000000000000000000");
    mbedtls_mpi_mul_int(&diff1, &diff1, 1000000);
    int diff_int = (int)(difficulty * 1000000);
    if (diff_int <= 0) diff_int = 1;
    mbedtls_mpi_lset(&pool_diff, diff_int);
    mbedtls_mpi_div_mpi(&result, NULL, &diff1, &pool_diff);
    mbedtls_mpi_write_binary(&result, target_out, 32);
    mbedtls_mpi_free(&diff1); mbedtls_mpi_free(&pool_diff); mbedtls_mpi_free(&result);
}

double calculate_current_hash_diff(uint8_t *hash) {
    mbedtls_mpi diff1, hash_mpi, result;
    mbedtls_mpi_init(&diff1); mbedtls_mpi_init(&hash_mpi); mbedtls_mpi_init(&result);
    mbedtls_mpi_read_string(&diff1, 16, "00000000FFFF0000000000000000000000000000000000000000000000000000");
    
    uint8_t hash_reversed[32];
    for(int i = 0; i < 32; i++) {
        hash_reversed[i] = hash[31 - i];
    }
    mbedtls_mpi_read_binary(&hash_mpi, hash_reversed, 32);
    if (mbedtls_mpi_cmp_int(&hash_mpi, 0) == 0) {
        mbedtls_mpi_free(&diff1); mbedtls_mpi_free(&hash_mpi); mbedtls_mpi_free(&result);
        return 0;
    }
    mbedtls_mpi_mul_int(&diff1, &diff1, 10000);
    mbedtls_mpi_div_mpi(&result, NULL, &diff1, &hash_mpi);
    char buf[64] = {0}; size_t olen = 0;
    mbedtls_mpi_write_string(&result, 10, buf, sizeof(buf), &olen);
    double res = atof(buf) / 10000.0;
    mbedtls_mpi_free(&diff1); mbedtls_mpi_free(&hash_mpi); mbedtls_mpi_free(&result);
    return res;
}

void init_uart()
{
    uart_config_t config = {.baud_rate = 115200, .data_bits = UART_DATA_8_BITS, .parity = UART_PARITY_DISABLE, .stop_bits = UART_STOP_BITS_1, .flow_ctrl = UART_HW_FLOWCTRL_DISABLE, .source_clk = UART_SCLK_DEFAULT};
    uart_param_config(UART_PORT, &config);
    uart_set_pin(UART_PORT, TXD_PIN, RXD_PIN, -1, -1);
    uart_driver_install(UART_PORT, 1024, 1024, 0, NULL, 0);
}

// ============================================================================
// WEB SERVER DASHBOARD
// ============================================================================
esp_err_t stats_get_handler(httpd_req_t *req)
{
    size_t buf_len = 8192; char *buf = calloc(buf_len, 1);
    if (!buf) return ESP_FAIL;

    uint32_t uptime_sec = (uint32_t)((esp_timer_get_time() - g_start_time) / 1000000);
    double hashrate = 0;
    if (uptime_sec > 0)
        hashrate = (double)g_shares_sent * g_pool_difficulty * 4294967296.0 / uptime_sec;

    char history_html[2048] = "";
    for (int i = 0; i < 4; i++) {
        if (strlen(g_last_accepted_times[i]) > 0) {
            strcat(history_html, "<li>"); strcat(history_html, g_last_accepted_times[i]); strcat(history_html, "</li>");
        }
    }

    snprintf(buf, buf_len,
             "<html><head><meta charset='UTF-8'><meta http-equiv='refresh' content='2'>"
             "<style>body{background:#121212;color:#e0e0e0;font-family:sans-serif;display:flex;justify-content:center;padding:20px;}"
             ".card{background:#1e1e1e;padding:30px;border-radius:15px;box-shadow:0 10px 30px rgba(0,0,0,0.5);width:450px;border-top:5px solid #00bcd4;}"
             "h1{color:#00bcd4;margin-top:0;} .stat{margin:15px 0;font-size:1.1em; border-bottom:1px solid #333; padding-bottom:5px;} .val{font-weight:bold;color:#fff;float:right;}"
             "ul{list-style:none;padding:0;font-size:0.9em;color:#888;} li{border-bottom:1px solid #333;padding:5px 0;}</style>"
             "<title>Bancada Gênesis FPGA</title></head><body><div class='card'>"
             "<h1>⛏️ Modo Teste Gênesis</h1>"
             "<div class='stat'>Status: <span class='val' style='color:#ff9800;'>INJETANDO LOOP 40S</span></div>"
             "<div class='stat'>Simulação Hashrate: <span class='val'>%.2f H/s</span></div>"
             "<div class='stat'>Diff do Alvo: <span class='val'>%.5f</span></div>"
             "<div class='stat'>Melhor Share: <span class='val' style='color:#ffeb3b;'>%.8f</span></div>"
             "<div class='stat'>Total Capturados: <span class='val'>%lu</span></div>"
             "<div class='stat'>Aceitos (Filtro OK): <span class='val' style='color:#4caf50;'>%lu</span></div>"
             "<div class='stat'>Rejeitados (Filtro Errado): <span class='val' style='color:#f44336;'>%lu</span></div>"
             "<div class='stat'>Uptime: <span class='val'>%lu s</span></div>"
             "<h3>🕒 Logs Recentes de Shares:</h3><ul>%s</ul>"
             "</div></body></html>",
             hashrate, g_pool_difficulty, g_best_diff,
             (unsigned long)g_shares_sent, (unsigned long)g_shares_accepted,
             (unsigned long)g_shares_rejected, (unsigned long)uptime_sec, history_html);

    httpd_resp_set_type(req, "text/html");
    httpd_resp_send(req, buf, strlen(buf));
    free(buf); return ESP_OK;
}

void start_webserver()
{
    httpd_handle_t server = NULL; httpd_config_t config = HTTPD_DEFAULT_CONFIG(); config.stack_size = 12288;
    if (httpd_start(&server, &config) == ESP_OK) {
        httpd_uri_t stats_uri = {.uri = "/", .method = HTTP_GET, .handler = stats_get_handler, .user_ctx = NULL};
        httpd_register_uri_handler(server, &stats_uri);
    }
}

// ============================================================================
// SIMULADOR INTERNO E MAESTRO DO BLOCO GÊNESIS
// ============================================================================
void inject_genesis_job()
{
    ESP_LOGW(TAG, "⚡ [Injeção Gênesis] Montando e enviando cabeçalho do Bloco 0 do Satoshi...");

    // Estrutura linear de 80 bytes do Bloco Gênesis Real do Bitcoin (Nonce inicializado em 0)
    uint8_t genesis_header[80] = {
        0x01, 0x00, 0x00, 0x00, // Version: 1
        // Previous Block Hash: 32 bytes de Zeros
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        // Merkle Root: 32 bytes oficiais (Já espelhados em Endianness)
        0x3B, 0xA3, 0xED, 0xFD, 0x7A, 0x7B, 0x12, 0xB2, 0x7A, 0xC7, 0x2C, 0x3E, 0x67, 0x76, 0x8F, 0x61, 
        0x7F, 0xC8, 0x1B, 0xC3, 0x88, 0x8A, 0x51, 0x32, 0x3A, 0x9F, 0xB8, 0xAA, 0x4B, 0x1E, 0x5E, 0x4A,
        0x29, 0xAB, 0x5F, 0x49, // Time: 1231006505
        0xFF, 0xFF, 0x00, 0x1D, // Bits: Dificuldade 1 Target
        0x00, 0x00, 0x00, 0x00  // Nonce: Começa varredura em 0
    };

    // Atualiza a prancheta global para o verificador local SHA256 saber conferir
    memcpy(g_current_header, genesis_header, 80);
    g_pool_difficulty = 1.0; 

    // Calcula o Midstate do Bloco Gênesis em tempo de execução
    uint8_t midstate[32] = {0};
    calculate_midstate(genesis_header, midstate);
    ESP_LOGW(TAG, "[genesis_header]");
    ESP_LOG_BUFFER_HEX(TAG, genesis_header, sizeof(genesis_header));
    ESP_LOGW(TAG, "[midstate]");
    ESP_LOG_BUFFER_HEX(TAG, midstate, sizeof(midstate));

    // Formata o pacote de 70 bytes do protocolo original do bitsyminers/fpgaminer
    uint8_t packet[70] = {0x55, 0xAA, 0x21, 0x42};
    memcpy(&packet[4], midstate, 32);
    memcpy(&packet[36], &genesis_header[64], 12);
    packet[69] = get_crc5(&packet[2], 67);

    // Limpa filas e joga no barramento UART1 com o Maestro
    uart_flush(UART_PORT);
    uart_write_bytes(UART_PORT, packet, 70);
    ESP_LOGI(TAG, ">> Packet Gênesis disparado! O Maestro vai acordar o motor Gowin.");
}

static void stratum_client_task(void *pvParameters)
{
    uint32_t last_send_time = 0;
    uint8_t resp[32];

    ESP_LOGI(TAG, "Módulo de Teste Criptográfico pronto. Forçando loop autônomo.");

    while (1)
    {
        uint32_t current_time = (uint32_t)(esp_timer_get_time() / 1000000);

        // Dispara e reinicia o Job a cada 40 segundos (Garante tempo de corrida pra FPGA!)
        if (last_send_time == 0 || (current_time - last_send_time) >= 40) {
            last_send_time = current_time;
            inject_genesis_job();
            ESP_LOGW(TAG, "Job genesis injetado");
        }

        // Fica vigiando se o Maestro devolveu as respostas da FPGA (Pacote de 11 bytes padrão Bitmain)
        if (uart_read_bytes(UART_PORT, resp, 11, 10 / portTICK_PERIOD_MS) == 11 && resp[0] == 0xAA && resp[1] == 0x55) {
            uint32_t nonce = (resp[4] << 24) | (resp[5] << 16) | (resp[6] << 8) | resp[7];
            ESP_LOGW(TAG, "Nonce recebido!");
            g_shares_sent++; // Estatística de recepção de ticket

            // Injeta o nonce recebido no final do g_current_header respeitando a ordem Little-Endian
            //1dac2b7c
            g_current_header[76] = resp[4]; // LSB // 0x1d;//
            g_current_header[77] = resp[5]; // 0xac;//
            g_current_header[78] = resp[6]; // 0x2b;//
            g_current_header[79] = resp[7]; // MSB // 0x7c;//
            
            // Calcula o Hash Total de 80 bytes do bloco inteiro via Software na CPU do ESP32
            uint8_t h_out[32]; 
            double_sha256(g_current_header, 80, h_out);
            
            // Calcula a dificuldade real alcançada por esse Hash
            double current_hash_diff = calculate_current_hash_diff(h_out);
            if (current_hash_diff > g_best_diff) {
                g_best_diff = current_hash_diff;
            }
            ESP_LOGW(TAG, "🏆 [h_out] %032lx gerou Diff %.4f!", (unsigned long)h_out, current_hash_diff);
            // Gera a máscara de comparação matemática do Target de Dificuldade
            uint8_t target[32];
            calculate_target(g_pool_difficulty, target);

            // RELIGAMOS O PRÉ-FILTRO! Validação oficial de dificuldade de hardware
            bool valid = false;
            for (int i = 0; i < 32; i++) {
                if (h_out[31 - i] < target[i]) { valid = true; break; }
                if (h_out[31 - i] > target[i]) { valid = false; break; }
            }

            // Grava os logs no Dashboard Web
            if (valid) {
                g_shares_accepted++;
                snprintf(g_last_accepted_times[g_accepted_idx], 64, "ACEITO: Nonce %08lX (Diff %.4f)", (unsigned long)nonce, current_hash_diff);
                g_accepted_idx = (g_accepted_idx + 1) % 4;
                ESP_LOGW(TAG, "🏆 [FILTRO APROVADO] A MÁGICA CONCORDEU! Nonce %08lx gerou Diff legítima de %.4f!", (unsigned long)nonce, current_hash_diff);
            } else {
                g_shares_rejected++;
                snprintf(g_last_accepted_times[g_accepted_idx], 64, "REJEITADO: Nonce %08lX (Diff %.4f)", (unsigned long)nonce, current_hash_diff);
                g_accepted_idx = (g_accepted_idx + 1) % 4;
                ESP_LOGE(TAG, "❌ [FILTRO REJEITOU] Erro de hash. O Nonce %08lx gerou Diff inválida de %.4f.", (unsigned long)nonce, current_hash_diff);
            }
        }
    }
}

static void wifi_event_handler(void *arg, esp_event_base_t event_base, int32_t event_id, void *event_data)
{
    if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_START)
        esp_wifi_connect();
    else if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_DISCONNECTED) {
        esp_wifi_connect();
        ESP_LOGI(TAG, "Reconectando ao Wi-Fi local...");
    }
    else if (event_base == IP_EVENT && event_id == IP_EVENT_STA_GOT_IP) {
        ip_event_got_ip_t *event = (ip_event_got_ip_t *)event_data;
        ESP_LOGI(TAG, "=================================================");
        ESP_LOGI(TAG, "📡 Wi-Fi OK! Endereço do Painel de Controle: " IPSTR, IP2STR(&event->ip_info.ip));
        ESP_LOGI(TAG, "👉 Abra http://" IPSTR " no seu navegador para ver o gráfico!", IP2STR(&event->ip_info.ip));
        ESP_LOGI(TAG, "=================================================");
    }
}

void app_main(void)
{
    g_start_time = esp_timer_get_time();
    init_uart();
    nvs_flash_init();
    esp_netif_init();
    esp_event_loop_create_default();
    esp_netif_create_default_wifi_sta();

    wifi_init_config_t cfg = WIFI_INIT_CONFIG_DEFAULT();
    esp_wifi_init(&cfg);

    esp_event_handler_instance_register(WIFI_EVENT, ESP_EVENT_ANY_ID, &wifi_event_handler, NULL, NULL);
    esp_event_handler_instance_register(IP_EVENT, IP_EVENT_STA_GOT_IP, &wifi_event_handler, NULL, NULL);

    wifi_config_t wifi_config = {.sta = {.ssid = WIFI_SSID, .password = WIFI_PASS}};
    esp_wifi_set_mode(WIFI_MODE_STA);
    esp_wifi_set_config(WIFI_IF_STA, &wifi_config);
    esp_wifi_start();

    vTaskDelay(3000 / portTICK_PERIOD_MS);
    start_webserver();
    
    // Inicia a tarefa de processamento e auditoria da FPGA
    xTaskCreate(stratum_client_task, "stratum_task", 20480, NULL, 5, NULL);
}