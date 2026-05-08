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

// --- CONFIGURAÇÕES DE REDE E POOL (Via Menuconfig) ---
#define WIFI_SSID CONFIG_WIFI_SSID
#define WIFI_PASS CONFIG_WIFI_PASSWORD
#define BTC_ADDRESS CONFIG_BTC_ADDRESS

#define POOL_URL "solo.ckpool.org"
#define POOL_PORT 3333
#define WORKER_NAME "minis3"

static const char *TAG = "MICRO_STRATUM";

// Handlers para o Wi-Fi
static void wifi_event_handler(void *arg, esp_event_base_t event_base, int32_t event_id, void *event_data)
{
    if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_START)
    {
        esp_wifi_connect();
    }
    else if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_DISCONNECTED)
    {
        esp_wifi_connect();
        ESP_LOGI(TAG, "Tentando reconectar ao Wi-Fi...");
    }
    else if (event_base == IP_EVENT && event_id == IP_EVENT_STA_GOT_IP)
    {
        ip_event_got_ip_t *event = (ip_event_got_ip_t *)event_data;
        ESP_LOGI(TAG, "Conectado! IP recebido: " IPSTR, IP2STR(&event->ip_info.ip));
    }
}

// Variáveis globais para guardar o que a pool nos deu no início
char g_extranonce1[32] = {0};
int g_extranonce2_size = 0;

// Função auxiliar para converter string Hex para Bytes binários
void hex_to_bytes(const char *hex, uint8_t *bytes)
{
    size_t len = strlen(hex);
    for (size_t i = 0; i < len; i += 2)
    {
        sscanf(hex + i, "%02hhx", &bytes[i / 2]);
    }
}

// Cálculo do Midstate usando a mbedTLS do ESP-IDF
void calculate_midstate(uint8_t *header, uint8_t *midstate)
{
    mbedtls_sha256_context ctx;
    mbedtls_sha256_init(&ctx);
    mbedtls_sha256_starts(&ctx, 0); // 0 para SHA-256 (não 224)

    // Processamos apenas os primeiros 64 bytes do cabeçalho de 80 bytes
    mbedtls_sha256_update(&ctx, header, 64);

    // Extraímos o estado interno (isso é o midstate)
    // Na mbedTLS, o estado fica no array 'state' do contexto
    for (int i = 0; i < 8; i++)
    {
        midstate[i * 4 + 0] = (uint8_t)(ctx.state[i] >> 0);
        midstate[i * 4 + 1] = (uint8_t)(ctx.state[i] >> 8);
        midstate[i * 4 + 2] = (uint8_t)(ctx.state[i] >> 16);
        midstate[i * 4 + 3] = (uint8_t)(ctx.state[i] >> 24);
    }
    mbedtls_sha256_free(&ctx);
}

// Função auxiliar para calcular o Duplo SHA-256
void double_sha256(const uint8_t *data, size_t len, uint8_t *out) {
    uint8_t hash1[32];
    mbedtls_sha256(data, len, hash1, 0); // Primeiro SHA-256
    mbedtls_sha256(hash1, 32, out, 0);   // Segundo SHA-256
}



void process_mining_notify(cJSON *params)
{
    // 0: Job ID, 1: PrevHash, 2: Coinb1, 3: Coinb2, 4: MerkleBranch, 5: Version, 6: nBits, 7: nTime
    const char *job_id = cJSON_GetArrayItem(params, 0)->valuestring;
    const char *prev_hash_hex = cJSON_GetArrayItem(params, 1)->valuestring;
    const char *version_hex = cJSON_GetArrayItem(params, 5)->valuestring;
    const char *nbits_hex = cJSON_GetArrayItem(params, 6)->valuestring;
    const char *ntime_hex = cJSON_GetArrayItem(params, 7)->valuestring;

    ESP_LOGI("STRATUM_PARSER", "Novo Trabalho: %s", job_id);

    // Simplificação para o Bitaxe: Montando o esqueleto do cabeçalho de 80 bytes
    uint8_t header[80] = {0};
    uint8_t midstate[32] = {0};

    // 1. Version (4 bytes)
    hex_to_bytes(version_hex, &header[0]);
    // 2. PrevHash (32 bytes)
    hex_to_bytes(prev_hash_hex, &header[4]);

    // Nota: O Merkle Root (32 bytes) viria aqui em header[36].
    // Para simplificar agora, vamos pular a árvore de Merkle e focar no midstate.

    // Calcula o Midstate (baseado nos primeiros 64 bytes do header)
    calculate_midstate(header, midstate);

    ESP_LOGI("STRATUM_PARSER", "Midstate Calculado!");
}

// A Tarefa (Thread) que fala com a Pool
static void stratum_client_task(void *pvParameters)
{
    char rx_buffer[1024];
    int addr_family = 0;
    int ip_protocol = 0;

    while (1)
    {
        struct hostent *hp = gethostbyname(POOL_URL);
        if (!hp)
        {
            ESP_LOGE(TAG, "Falha ao resolver DNS da pool");
            vTaskDelay(2000 / portTICK_PERIOD_MS);
            continue;
        }

        struct sockaddr_in dest_addr;
        inet_pton(AF_INET, inet_ntoa(*(struct in_addr *)hp->h_addr), &dest_addr.sin_addr);
        dest_addr.sin_family = AF_INET;
        dest_addr.sin_port = htons(POOL_PORT);
        addr_family = AF_INET;
        ip_protocol = IPPROTO_IP;

        int sock = socket(addr_family, SOCK_STREAM, ip_protocol);
        if (sock < 0)
        {
            ESP_LOGE(TAG, "Falha ao criar socket TCP");
            break;
        }
        ESP_LOGI(TAG, "Socket criado. Conectando a %s:%d...", POOL_URL, POOL_PORT);

        int err = connect(sock, (struct sockaddr *)&dest_addr, sizeof(struct sockaddr_in));
        if (err != 0)
        {
            ESP_LOGE(TAG, "Falha ao conectar: errno %d", errno);
            close(sock);
            vTaskDelay(2000 / portTICK_PERIOD_MS);
            continue;
        }
        ESP_LOGI(TAG, "Conectado com sucesso à Pool!");

        // --- PROTOCOLO STRATUM (HANDSHAKE) ---
        // 1. Comando de Subscribe (Avisando a pool que queremos trabalhos)
        const char *subscribe_msg = "{\"id\": 1, \"method\": \"mining.subscribe\", \"params\": []}\n";
        send(sock, subscribe_msg, strlen(subscribe_msg), 0);
        ESP_LOGI(TAG, "=> Enviado: mining.subscribe");

        // 2. Comando de Authorize (Identificando o usuário/carteira)
        char auth_msg[200];
        snprintf(auth_msg, sizeof(auth_msg), "{\"id\": 2, \"method\": \"mining.authorize\", \"params\": [\"%s.%s\", \"x\"]}\n", BTC_ADDRESS, WORKER_NAME);
        send(sock, auth_msg, strlen(auth_msg), 0);
        ESP_LOGI(TAG, "=> Enviado: mining.authorize");

        // --- LOOP DE ESCUTA (Acumulador de Linhas Stratum) ---
        // Aumentamos o buffer para 4096 para caber a árvore de Merkle inteira
        char *rx_buffer = calloc(4096, sizeof(char));
        int rx_len = 0;

        while (1)
        {
            // Lê o que chegou da rede e coloca no final do que já temos
            int len = recv(sock, rx_buffer + rx_len, 4096 - rx_len - 1, 0);
            if (len < 0)
            {
                ESP_LOGE(TAG, "Erro na recepção dos dados: errno %d", errno);
                break;
            }
            else if (len == 0)
            {
                ESP_LOGW(TAG, "A conexão foi fechada pela Pool.");
                break;
            }

            rx_len += len;
            rx_buffer[rx_len] = '\0'; // Garante o fim da string

            // Procura por uma quebra de linha (Fim do JSON)
            char *newline;
            while ((newline = strchr(rx_buffer, '\n')) != NULL)
            {
                *newline = '\0'; // Corta a string exatamente aqui

                // AGORA TEMOS UM JSON COMPLETO! Vamos parsear:
                cJSON *json = cJSON_Parse(rx_buffer);
                if (json)
                {
                    cJSON *method = cJSON_GetObjectItem(json, "method");
                    if (method && strcmp(method->valuestring, "mining.notify") == 0)
                    {
                        process_mining_notify(cJSON_GetObjectItem(json, "params"));
                    }

                    cJSON *id = cJSON_GetObjectItem(json, "id");
                    if (id && id->valueint == 1)
                    {
                        cJSON *result = cJSON_GetObjectItem(json, "result");
                        if (cJSON_IsArray(result))
                        {
                            strcpy(g_extranonce1, cJSON_GetArrayItem(result, 1)->valuestring);
                            g_extranonce2_size = cJSON_GetArrayItem(result, 2)->valueint;
                            ESP_LOGI(TAG, "Extranonce1 capturado: %s", g_extranonce1);
                        }
                    }
                    cJSON_Delete(json); // Limpa a memória do JSON
                }
                else
                {
                    ESP_LOGE(TAG, "Falha ao ler JSON (pode estar mal formatado)");
                }

                // Empurra o restante dos dados (se houver) para o início do buffer
                int remaining = rx_len - (newline - rx_buffer) - 1;
                if (remaining > 0)
                {
                    memmove(rx_buffer, newline + 1, remaining);
                }
                rx_len = remaining;
                rx_buffer[rx_len] = '\0';
            }
        }
        free(rx_buffer);

        if (sock != -1)
        {
            ESP_LOGE(TAG, "Desligando socket e reiniciando...");
            shutdown(sock, 0);
            close(sock);
        }
    }
    vTaskDelete(NULL);
}

void app_main(void)
{
    // Inicializa a memória não-volátil (necessário para o Wi-Fi)
    ESP_ERROR_CHECK(nvs_flash_init());
    ESP_ERROR_CHECK(esp_netif_init());
    ESP_ERROR_CHECK(esp_event_loop_create_default());
    esp_netif_create_default_wifi_sta();

    // Configura o Wi-Fi
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

    // Inicia a tarefa do Stratum após 5 segundos para garantir a conexão Wi-Fi
    vTaskDelay(5000 / portTICK_PERIOD_MS);
    xTaskCreate(stratum_client_task, "stratum_task", 4096, NULL, 5, NULL);
}