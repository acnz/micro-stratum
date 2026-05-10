#include <string.h>
#include <sys/param.h>
#include <math.h> // Necessário para calcular a Dificuldade da Rede
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
#define TXD_PIN CONFIG_UART_TXD // Confirme se no C3 você está usando os pinos corretos
#define RXD_PIN CONFIG_UART_RXD
#define UART_PORT UART_NUM_1

#define WIFI_SSID CONFIG_WIFI_SSID
#define WIFI_PASS CONFIG_WIFI_PASSWORD
#define BTC_ADDRESS CONFIG_BTC_ADDRESS
#define POOL_URL CONFIG_POOL_URL
#define POOL_PORT CONFIG_POOL_PORT
#define WORKER_NAME CONFIG_WORKER_NAME

static const char *TAG = "MICRO_STRATUM";

// --- ESTATÍSTICAS GLOBAIS ---
uint32_t g_shares_accepted = 0;
uint32_t g_shares_rejected = 0;
int64_t g_start_time = 0;
char g_last_accepted_times[10][64];
int g_accepted_idx = 0;

double g_pool_difficulty = 1.0;
double g_network_difficulty = 0.0; // Nova variável global
double g_network_odds = 0.0;       // Nova variável global

uint8_t g_current_header[80] = {0};
char g_last_job_id[32] = {0};
char g_last_ntime[16] = {0};
char g_extranonce1[32] = {0};
int g_extranonce2_size = 0;

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
    uint32_t a, b, c, d, e, f, g, h, i, T1, T2, W[64];
    for (i = 0; i < 16; i++) W[i] = (data[i * 4] << 24) | (data[i * 4 + 1] << 16) | (data[i * 4 + 2] << 8) | data[i * 4 + 3];
    for (i = 16; i < 64; i++) W[i] = SIG1(W[i - 2]) + W[i - 7] + SIG0(W[i - 15]) + W[i - 16];
    a = state[0]; b = state[1]; c = state[2]; d = state[3]; e = state[4]; f = state[5]; g = state[6]; h = state[7];
    for (i = 0; i < 64; i++) {
        T1 = h + EP1(e) + CH(e, f, g) + sha256_k[i] + W[i];
        T2 = EP0(a) + MAJ(a, b, c);
        h = g; g = f; f = e; e = d + T1; d = c; c = b; b = a; a = T1 + T2;
    }
    state[0] += a; state[1] += b; state[2] += c; state[3] += d; state[4] += e; state[5] += f; state[6] += g; state[7] += h;
}

void calculate_midstate(const uint8_t *header64, uint8_t *midstate_out) {
    uint32_t state[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
    sha256_transform(state, header64);
    for(int i=0; i<8; i++) {
        midstate_out[i*4] = (state[i] >> 24) & 0xFF; midstate_out[i*4+1] = (state[i] >> 16) & 0xFF;
        midstate_out[i*4+2] = (state[i] >> 8) & 0xFF; midstate_out[i*4+3] = state[i] & 0xFF;
    }
}

// ============================================================================
// FUNÇÕES AUXILIARES
// ============================================================================
uint8_t get_crc5(uint8_t *ptr, uint8_t len) {
    uint8_t i, j, crc = 0x1f;
    for (i = 0; i < len; i++) {
        crc ^= ptr[i];
        for (j = 0; j < 8; j++) { if (crc & 0x80) crc = (crc << 1) ^ 0x05; else crc <<= 1; }
    }
    return ((crc >> 3) & 0x1f);
}

void hex_to_bytes(const char *hex, uint8_t *bytes) {
    size_t len = strlen(hex);
    for (size_t i = 0; i < len / 2; i++) {
        char high = hex[i * 2], low = hex[i * 2 + 1];
        uint8_t h = (high >= '0' && high <= '9') ? (high - '0') : (high >= 'a' && high <= 'f') ? (high - 'a' + 10) : (high >= 'A' && high <= 'F') ? (high - 'A' + 10) : 0;
        uint8_t l = (low >= '0' && low <= '9') ? (low - '0') : (low >= 'a' && low <= 'f') ? (low - 'a' + 10) : (low >= 'A' && low <= 'F') ? (low - 'A' + 10) : 0;
        bytes[i] = (h << 4) | l;
    }
}

void double_sha256(const uint8_t *data, size_t len, uint8_t *out) {
    uint8_t h1[32]; mbedtls_sha256(data, len, h1, 0); mbedtls_sha256(h1, 32, out, 0);
}

void calculate_target(double difficulty, uint8_t *target_out) {
    mbedtls_mpi diff1, pool_diff, result;
    mbedtls_mpi_init(&diff1); mbedtls_mpi_init(&pool_diff); mbedtls_mpi_init(&result);
    mbedtls_mpi_read_string(&diff1, 16, "00000000FFFF0000000000000000000000000000000000000000000000000000");
    mbedtls_mpi_mul_int(&diff1, &diff1, 1000000); // 1 MILHÃO para aguentar dif < 1
    int diff_int = (int)(difficulty * 1000000);
    if(diff_int <= 0) diff_int = 1; 
    mbedtls_mpi_lset(&pool_diff, diff_int);
    mbedtls_mpi_div_mpi(&result, NULL, &diff1, &pool_diff);
    mbedtls_mpi_write_binary(&result, target_out, 32);
    mbedtls_mpi_free(&diff1); mbedtls_mpi_free(&pool_diff); mbedtls_mpi_free(&result);
}

void init_uart() {
    uart_config_t config = { .baud_rate = 115200, .data_bits = UART_DATA_8_BITS, .parity = UART_PARITY_DISABLE, .stop_bits = UART_STOP_BITS_1, .flow_ctrl = UART_HW_FLOWCTRL_DISABLE, .source_clk = UART_SCLK_DEFAULT };
    uart_param_config(UART_PORT, &config);
    uart_set_pin(UART_PORT, TXD_PIN, RXD_PIN, -1, -1);
    uart_driver_install(UART_PORT, 1024, 1024, 0, NULL, 0);
}

// ============================================================================
// WEB SERVER DASHBOARD
// ============================================================================
esp_err_t stats_get_handler(httpd_req_t *req) {
    size_t buf_len = 8192;
    char *buf = calloc(buf_len, 1);
    if (!buf) return ESP_FAIL;
    
    uint32_t uptime_sec = (uint32_t)((esp_timer_get_time() - g_start_time) / 1000000);
    double hashrate = 0;
    if (uptime_sec > 0) hashrate = (double)g_shares_accepted * g_pool_difficulty * 4294967296.0 / uptime_sec;

    // Converte para Trilhões (T) para ficar legível
    double net_diff_t = g_network_difficulty / 1000000000000.0;

    char history_html[2048] = "";
    for(int i=0; i<10; i++) {
        if(strlen(g_last_accepted_times[i]) > 0) {
            strcat(history_html, "<li>"); strcat(history_html, g_last_accepted_times[i]); strcat(history_html, "</li>");
        }
    }

    snprintf(buf, buf_len,
        "<html><head><meta charset='UTF-8'><meta http-equiv='refresh' content='5'>"
        "<style>body{background:#121212;color:#e0e0e0;font-family:sans-serif;display:flex;justify-content:center;padding:20px;}"
        ".card{background:#1e1e1e;padding:30px;border-radius:15px;box-shadow:0 10px 30px rgba(0,0,0,0.5);width:450px;border-top:5px solid #f2a900;}"
        "h1{color:#f2a900;margin-top:0;} .stat{margin:15px 0;font-size:1.1em; border-bottom:1px solid #333; padding-bottom:5px;} .val{font-weight:bold;color:#fff;float:right;}"
        "ul{list-style:none;padding:0;font-size:0.9em;color:#888;} li{border-bottom:1px solid #333;padding:5px 0;}</style>"
        "<title>ESP-Miner Dashboard</title></head><body><div class='card'>"
        "<h1>⛏️ Micro-Stratum</h1>"
        "<div class='stat'>Status: <span class='val' style='color:#4caf50;'>MINERANDO</span></div>"
        "<div class='stat'>Carteira: <span class='val' style='font-size:0.7em; color:#f2a900;'>%s</span></div>"
        "<div class='stat'>Pool: <span class='val'>%s:%d</span></div>"
        "<div class='stat'>Hashrate Est.: <span class='val'>%.2f H/s</span></div>"
        "<div class='stat'>Diff da Pool: <span class='val'>%.5f</span></div>"
        "<div class='stat'>Diff da Rede: <span class='val'>%.2f T</span></div>"
        "<div class='stat'>Loteria (Bloco): <span class='val' style='font-size:0.9em; color:#03dac6;'>1 em %.2e</span></div>"
        "<div class='stat'>Total Shares: <span class='val'>%lu</span></div>"
        "<div class='stat'>Aceitos: <span class='val' style='color:#4caf50;'>%lu</span></div>"
        "<div class='stat'>Rejeitados (Brain): <span class='val' style='color:#f44336;'>%lu</span></div>"
        "<div class='stat'>Uptime: <span class='val'>%lu s</span></div>"
        "<h3>🕒 Últimos Shares Aceitos:</h3><ul>%s</ul>"
        "</div></body></html>",
        BTC_ADDRESS, POOL_URL, POOL_PORT, hashrate, g_pool_difficulty, net_diff_t, g_network_odds,
        (unsigned long)(g_shares_accepted + g_shares_rejected), (unsigned long)g_shares_accepted, 
        (unsigned long)g_shares_rejected, (unsigned long)uptime_sec, history_html
    );

    httpd_resp_set_type(req, "text/html");
    httpd_resp_send(req, buf, strlen(buf));
    free(buf);
    return ESP_OK;
}

void start_webserver() {
    httpd_handle_t server = NULL;
    httpd_config_t config = HTTPD_DEFAULT_CONFIG();
    config.stack_size = 12288;
    if (httpd_start(&server, &config) == ESP_OK) {
        httpd_uri_t stats_uri = { .uri = "/", .method = HTTP_GET, .handler = stats_get_handler, .user_ctx = NULL };
        httpd_register_uri_handler(server, &stats_uri);
    }
}

// ============================================================================
// STRATUM PARSER & CLIENT
// ============================================================================
void process_mining_notify(cJSON *params) {
    if (!params || !cJSON_IsArray(params) || cJSON_GetArraySize(params) < 8) return;

    cJSON *j_job = cJSON_GetArrayItem(params, 0); cJSON *j_prev = cJSON_GetArrayItem(params, 1);
    cJSON *j_cb1 = cJSON_GetArrayItem(params, 2); cJSON *j_cb2 = cJSON_GetArrayItem(params, 3);
    cJSON *j_merkle = cJSON_GetArrayItem(params, 4); cJSON *j_ver = cJSON_GetArrayItem(params, 5);
    cJSON *j_nbits = cJSON_GetArrayItem(params, 6); cJSON *j_ntime = cJSON_GetArrayItem(params, 7);

    if (!cJSON_IsString(j_job) || !cJSON_IsString(j_prev) || !cJSON_IsString(j_cb1) || !cJSON_IsString(j_cb2) || !cJSON_IsArray(j_merkle)) return;

    char *coinbase_hex = calloc(2048, 1);
    uint8_t *coinbase_bin = calloc(1024, 1);
    if (!coinbase_hex || !coinbase_bin) { if(coinbase_hex) free(coinbase_hex); if(coinbase_bin) free(coinbase_bin); return; }

    uint8_t current_hash[32];
    strcat(coinbase_hex, j_cb1->valuestring); strcat(coinbase_hex, g_extranonce1); 
    strcat(coinbase_hex, "00000000"); strcat(coinbase_hex, j_cb2->valuestring);
    
    hex_to_bytes(coinbase_hex, coinbase_bin);
    double_sha256(coinbase_bin, strlen(coinbase_hex)/2, current_hash);
    
    free(coinbase_hex); free(coinbase_bin);

    for (int i = 0; i < cJSON_GetArraySize(j_merkle); i++) {
        uint8_t branch_bin[32], combined[64];
        cJSON *branch_item = cJSON_GetArrayItem(j_merkle, i);
        if (cJSON_IsString(branch_item)) {
            hex_to_bytes(branch_item->valuestring, branch_bin);
            memcpy(combined, current_hash, 32); memcpy(combined + 32, branch_bin, 32);
            double_sha256(combined, 64, current_hash);
        }
    }

    uint8_t header[80] = {0};
    if (cJSON_IsString(j_ver) && cJSON_IsString(j_nbits) && cJSON_IsString(j_ntime)) {
        
        // --- CÁLCULO DA DIFICULDADE DA REDE (A Mágica da Loteria) ---
        const char* nbits_str = j_nbits->valuestring;
        if (strlen(nbits_str) >= 8) {
            char hex_exp[3] = { nbits_str[0], nbits_str[1], 0 };
            char hex_man[7] = { nbits_str[2], nbits_str[3], nbits_str[4], nbits_str[5], nbits_str[6], nbits_str[7], 0 };
            long exponent = strtol(hex_exp, NULL, 16);
            long mantissa = strtol(hex_man, NULL, 16);
            if (mantissa > 0) {
                // Formula oficial do protocolo Bitcoin
                g_network_difficulty = 65535.0 * pow(256.0, 29.0 - exponent) / mantissa;
                g_network_odds = g_network_difficulty * 4294967296.0;
            }
        }
        
        hex_to_bytes(j_ver->valuestring, &header[0]);   
        hex_to_bytes(j_prev->valuestring, &header[4]); 
        memcpy(&header[36], current_hash, 32);   
        hex_to_bytes(j_ntime->valuestring, &header[68]);    
        hex_to_bytes(j_nbits->valuestring, &header[72]);    

        memcpy(g_current_header, header, 80);
        strncpy(g_last_job_id, j_job->valuestring, 31);
        strncpy(g_last_ntime, j_ntime->valuestring, 15);

        uint8_t midstate[32] = {0}; calculate_midstate(header, midstate);
        uint8_t packet[70] = {0x55, 0xAA, 0x21, 0x42};
        memcpy(&packet[4], midstate, 32); memcpy(&packet[36], &header[64], 12);
        packet[69] = get_crc5(&packet[2], 67);
        uart_write_bytes(UART_PORT, packet, 70);
        ESP_LOGI(TAG, "=> Trabalho ID [%s] enviado para o Músculo S3 fritar!", g_last_job_id);
    }
}

static void stratum_client_task(void *pvParameters) {
    char *rx = calloc(4096, 1);
    if(!rx) { ESP_LOGE(TAG, "Falha crítica de RAM."); vTaskDelete(NULL); }

    while (1) {
        struct hostent *hp = gethostbyname(POOL_URL);
        if (!hp) { vTaskDelay(2000 / portTICK_PERIOD_MS); continue; }
        
        struct sockaddr_in addr = { .sin_family = AF_INET, .sin_port = htons(POOL_PORT) };
        inet_pton(AF_INET, inet_ntoa(*(struct in_addr *)hp->h_addr), &addr.sin_addr);
        
        int sock = socket(AF_INET, SOCK_STREAM, 0);
        if (connect(sock, (struct sockaddr *)&addr, sizeof(addr)) != 0) { close(sock); vTaskDelay(2000/portTICK_PERIOD_MS); continue; }
        
        const char *sub_msg = "{\"id\": 1, \"method\": \"mining.subscribe\", \"params\": [\"MicroStratum/1.0\"]}\n";
        send(sock, sub_msg, strlen(sub_msg), 0);
        
        char auth[256]; snprintf(auth, 256, "{\"id\": 2, \"method\": \"mining.authorize\", \"params\": [\"%s.%s\", \"x\"]}\n", BTC_ADDRESS, WORKER_NAME);
        send(sock, auth, strlen(auth), 0);

        char suggest[128]; snprintf(suggest, 128, "{\"id\": 3, \"method\": \"mining.suggest_difficulty\", \"params\": [0.00015]}\n");
        send(sock, suggest, strlen(suggest), 0);

        int rx_len = 0; memset(rx, 0, 4096);
        int64_t last_keepalive = esp_timer_get_time();
        
        while (1) {
            int len = recv(sock, rx + rx_len, 4096 - rx_len - 1, MSG_DONTWAIT);
            
            if (len == 0) { ESP_LOGE(TAG, "💀 Conexão morta pela Pool! Reconectando..."); break; } 
            else if (len < 0 && errno != EAGAIN && errno != EWOULDBLOCK && errno != 11) { ESP_LOGE(TAG, "⚠️ Erro de rede! Reconectando..."); break; } 
            else if (len > 0) {
                rx_len += len; rx[rx_len] = '\0';
                char *nl;
                while ((nl = strchr(rx, '\n'))) {
                    *nl = '\0'; cJSON *j = cJSON_Parse(rx);
                    if (j) {
                        cJSON *m = cJSON_GetObjectItem(j, "method");
                        if (m && cJSON_IsString(m)) {
                            if (!strcmp(m->valuestring, "mining.notify")) process_mining_notify(cJSON_GetObjectItem(j, "params"));
                            else if (!strcmp(m->valuestring, "mining.set_difficulty")) g_pool_difficulty = cJSON_GetArrayItem(cJSON_GetObjectItem(j, "params"), 0)->valuedouble;
                        }
                        cJSON *id = cJSON_GetObjectItem(j, "id");
                        if (id && id->valueint == 1) {
                            cJSON *res = cJSON_GetObjectItem(j, "result");
                            if (cJSON_IsArray(res) && cJSON_GetArraySize(res) >= 3) { 
                                cJSON *extra = cJSON_GetArrayItem(res, 1);
                                if (cJSON_IsString(extra)) strcpy(g_extranonce1, extra->valuestring); 
                            }
                        }
                        cJSON_Delete(j);
                    }
                    int rem = rx_len - (nl - rx) - 1;
                    if (rem > 0) memmove(rx, nl + 1, rem);
                    rx_len = rem; rx[rx_len] = '\0';
                }
                if (rx_len > 4000) rx_len = 0; 
            }

            // --- ESCUTA ASSÍNCRONA DO MÚSCULO E JULGAMENTO DO HASH ---
            uint8_t resp[32];
            if (uart_read_bytes(UART_PORT, resp, 11, 10 / portTICK_PERIOD_MS) == 11 && resp[0] == 0xAA && resp[1] == 0x55) {
                uint32_t nonce = (resp[4] << 24) | (resp[5] << 16) | (resp[6] << 8) | resp[7];
                
                g_current_header[76] = resp[7]; g_current_header[77] = resp[6]; g_current_header[78] = resp[5]; g_current_header[79] = resp[4];
                uint8_t h_out[32]; double_sha256(g_current_header, 80, h_out);
                uint8_t target[32]; calculate_target(g_pool_difficulty, target);
                
                bool valid = false;
                for (int i = 0; i < 32; i++) { if (h_out[31-i] < target[i]) { valid = true; break; } if (h_out[31-i] > target[i]) { valid = false; break; } }
                
                if (valid) {
                    g_shares_accepted++;
                    snprintf(g_last_accepted_times[g_accepted_idx], 64, "Share #%lu em %lu s (Diff %.5f)", (unsigned long)g_shares_accepted, (unsigned long)((esp_timer_get_time() - g_start_time)/1000000), g_pool_difficulty);
                    g_accepted_idx = (g_accepted_idx + 1) % 10;
                    char sub[256]; snprintf(sub, 256, "{\"id\": 4, \"method\": \"mining.submit\", \"params\": [\"%s.%s\", \"%s\", \"00000000\", \"%s\", \"%08lx\"]}\n", BTC_ADDRESS, WORKER_NAME, g_last_job_id, g_last_ntime, (unsigned long)nonce);
                    send(sock, sub, strlen(sub), 0);
                    ESP_LOGW(TAG, "🚀 SHARE ACEITO PELA POOL! Nonce: %08lx", (unsigned long)nonce);
                } else {
                    g_shares_rejected++;
                }
            }
            
            if ((esp_timer_get_time() - last_keepalive) > 30000000) { 
                char keepalive_msg[128];
                snprintf(keepalive_msg, sizeof(keepalive_msg), "{\"id\": 5, \"method\": \"mining.suggest_difficulty\", \"params\": [%.5f]}\n", g_pool_difficulty);
                send(sock, keepalive_msg, strlen(keepalive_msg), 0);
                last_keepalive = esp_timer_get_time();
            }
        }
        close(sock);
    }
}

// --- HANDLER DE EVENTOS DO WI-FI (AQUI ELE MOSTRA O IP!) ---
static void wifi_event_handler(void *arg, esp_event_base_t event_base, int32_t event_id, void *event_data) {
    if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_START) esp_wifi_connect();
    else if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_DISCONNECTED) {
        esp_wifi_connect(); ESP_LOGI(TAG, "Tentando reconectar ao Wi-Fi...");
    }
    else if (event_base == IP_EVENT && event_id == IP_EVENT_STA_GOT_IP) {
        ip_event_got_ip_t *event = (ip_event_got_ip_t *)event_data;
        ESP_LOGI(TAG, "========================================");
        ESP_LOGI(TAG, "📡 Conectado! IP do Dashboard: " IPSTR, IP2STR(&event->ip_info.ip));
        ESP_LOGI(TAG, "👉 Acesse http://" IPSTR " no seu navegador!", IP2STR(&event->ip_info.ip));
        ESP_LOGI(TAG, "========================================");
    }
}

void app_main(void) {
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

    wifi_config_t wifi_config = { .sta = { .ssid = WIFI_SSID, .password = WIFI_PASS } };
    esp_wifi_set_mode(WIFI_MODE_STA);
    esp_wifi_set_config(WIFI_IF_STA, &wifi_config);
    esp_wifi_start();

    vTaskDelay(5000 / portTICK_PERIOD_MS);
    start_webserver(); 
    xTaskCreate(stratum_client_task, "stratum_task", 20480, NULL, 5, NULL);
}