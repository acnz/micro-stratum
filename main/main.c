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

// --- CONFIGURAÇÕES DE REDE E POOL (Via Menuconfig) ---
#define WIFI_SSID CONFIG_WIFI_SSID
#define WIFI_PASS CONFIG_WIFI_PASSWORD
#define BTC_ADDRESS CONFIG_BTC_ADDRESS

#define POOL_URL "solo.ckpool.org"
#define POOL_PORT 3333
#define WORKER_NAME "MS-minis3"

// Variáveis de Memória do Cérebro
double g_pool_difficulty = 1.0;
uint8_t g_current_header[80] = {0};

static const char *TAG = "MICRO_STRATUM";

static const uint32_t sha256_initial_hash[8] = {
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
};

void calculate_midstate(const uint8_t *header64, uint8_t *midstate_out) {
    uint32_t state[8];
    memcpy(state, sha256_initial_hash, 32);
    
    // Calcula o Midstate usando a matemática de software
    sha256_transform(state, header64);
    
    // Converte de volta para bytes para enviar pela Serial
    for(int i=0; i<8; i++) {
        midstate_out[i*4]   = (state[i] >> 24) & 0xFF;
        midstate_out[i*4+1] = (state[i] >> 16) & 0xFF;
        midstate_out[i*4+2] = (state[i] >> 8)  & 0xFF;
        midstate_out[i*4+3] = (state[i] >> 0)  & 0xFF;
    }
}

// Função oficial de CRC5 da Bitmain
uint8_t get_crc5(uint8_t *ptr, uint8_t len)
{
    uint8_t i, j;
    uint8_t crc = 0x1f;
    for (i = 0; i < len; i++)
    {
        crc ^= ptr[i];
        for (j = 0; j < 8; j++)
        {
            if (crc & 0x80)
                crc = (crc << 1) ^ 0x05;
            else
                crc <<= 1;
        }
    }
    return ((crc >> 3) & 0x1f);
}

// Converte a Dificuldade da Pool para um Alvo de 256 bytes (Big-Endian)
void calculate_target(double difficulty, uint8_t *target_out)
{
    memset(target_out, 0, 32);
    if (difficulty <= 0.0)
        difficulty = 1.0;

    mbedtls_mpi diff1, pool_diff, result;
    mbedtls_mpi_init(&diff1);
    mbedtls_mpi_init(&pool_diff);
    mbedtls_mpi_init(&result);

    // O Target da Dificuldade 1 (O padrão máximo do Bitcoin)
    mbedtls_mpi_read_string(&diff1, 16, "00000000FFFF0000000000000000000000000000000000000000000000000000");

    // Matemática: Target = Diff_1 / Pool_Diff
    // Multiplicamos por 1000 para preservar casas decimais (ex: diff 0.1 vira 100)
    mbedtls_mpi_mul_int(&diff1, &diff1, 1000);
    int diff_int = (int)(difficulty * 1000);

    mbedtls_mpi_lset(&pool_diff, diff_int);
    mbedtls_mpi_div_mpi(&result, NULL, &diff1, &pool_diff);

    // Guarda o resultado no array de 32 bytes
    mbedtls_mpi_write_binary(&result, target_out, 32);

    mbedtls_mpi_free(&diff1);
    mbedtls_mpi_free(&pool_diff);
    mbedtls_mpi_free(&result);
}

// Inicialização da Porta Serial (UART)
void init_uart()
{
    uart_config_t uart_config = {
        .baud_rate = 115200, // Baudrate inicial de comunicação
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

// Função de Teste Físico da UART (Com detector de lixo)
void test_uart_ping_pong()
{
    ESP_LOGW("UART_TEST", "--- INICIANDO TESTE FÍSICO PING-PONG ---");
    ESP_LOGI("UART_TEST", "Enviando 'PING' para o C3...");

    // Limpa o buffer para não ler lixo antigo
    uart_flush(UART_PORT);

    // Envia o PING
    const char *ping_msg = "PING";
    uart_write_bytes(UART_PORT, ping_msg, 4);

    // Buffer maior para caso o C3 mande os logs de boot por engano
    uint8_t rx_buf[128];
    memset(rx_buf, 0, sizeof(rx_buf)); // Zera o buffer

    // Espera até 2 segundos pela resposta
    int len = uart_read_bytes(UART_PORT, rx_buf, sizeof(rx_buf) - 1, 2000 / portTICK_PERIOD_MS);

    if (len > 0)
    {
        rx_buf[len] = '\0'; // Transforma em string

        // Verifica se a palavra PONG está no meio do que chegou
        if (strstr((char *)rx_buf, "PONG") != NULL)
        {
            ESP_LOGI("UART_TEST", "SUCESSO ABSOLUTO! Recebido: %s", rx_buf);
        }
        else
        {
            ESP_LOGE("UART_TEST", "FALHA! Recebido %d bytes de 'lixo' em vez de PONG.", len);
            ESP_LOGW("UART_TEST", "Imprimindo o lixo em Hexadecimal para análise:");

            // Essa linha imprime os bytes brutos no terminal (ex: 41 42 43...)
            ESP_LOG_BUFFER_HEX("UART_TEST_HEX", rx_buf, len);

            ESP_LOGW("UART_TEST", "Imprimindo o lixo como texto (pode bugar o terminal):");
            printf("%s\n", rx_buf);
        }
    }
    else
    {
        ESP_LOGE("UART_TEST", "FALHA! Sem resposta (Timeout de 2 segundos).");
    }
    ESP_LOGW("UART_TEST", "----------------------------------------");
}

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

// Função auxiliar para calcular o Duplo SHA-256
void double_sha256(const uint8_t *data, size_t len, uint8_t *out)
{
    uint8_t hash1[32];
    mbedtls_sha256(data, len, hash1, 0); // Primeiro SHA-256
    mbedtls_sha256(hash1, 32, out, 0);   // Segundo SHA-256
}

void process_mining_notify(cJSON *params, int sock)
{
    // 0: Job ID, 1: PrevHash, 2: Coinb1, 3: Coinb2, 4: MerkleBranch, 5: Version, 6: nBits, 7: nTime
    const char *job_id = cJSON_GetArrayItem(params, 0)->valuestring;
    const char *prev_hash_hex = cJSON_GetArrayItem(params, 1)->valuestring;
    const char *coinb1 = cJSON_GetArrayItem(params, 2)->valuestring;
    const char *coinb2 = cJSON_GetArrayItem(params, 3)->valuestring;
    cJSON *merkle_branches = cJSON_GetArrayItem(params, 4);

    ESP_LOGI("STRATUM_PARSER", "Novo Trabalho Recebido: %s", job_id);

    // 1. Gerar o Extranonce2 (Fixo em zeros para simplificar o nosso simulador)
    // Se a Pool pediu 4 bytes (g_extranonce2_size == 4), enviamos 8 caracteres hex.
    char extranonce2_hex[9] = "00000000";

    // 2. Montar a Transação Coinbase completa
    size_t coinb_len = strlen(coinb1) + strlen(g_extranonce1) + strlen(extranonce2_hex) + strlen(coinb2);
    char *coinbase_hex = malloc(coinb_len + 1);
    strcpy(coinbase_hex, coinb1);
    strcat(coinbase_hex, g_extranonce1);
    strcat(coinbase_hex, extranonce2_hex);
    strcat(coinbase_hex, coinb2);

    // Converter a Coinbase de Texto Hexadecimal para Binário
    size_t coinbase_bin_len = coinb_len / 2;
    uint8_t *coinbase_bin = malloc(coinbase_bin_len);
    hex_to_bytes(coinbase_hex, coinbase_bin);

    // 3. O Hash Base (Duplo SHA-256 da Coinbase)
    uint8_t current_hash[32];
    double_sha256(coinbase_bin, coinbase_bin_len, current_hash);

    free(coinbase_hex);
    free(coinbase_bin);

    // 4. A Escalada da Árvore de Merkle
    int branch_count = cJSON_GetArraySize(merkle_branches);
    uint8_t branch_bin[32];
    uint8_t combined[64];

    for (int i = 0; i < branch_count; i++)
    {
        const char *branch_hex = cJSON_GetArrayItem(merkle_branches, i)->valuestring;
        hex_to_bytes(branch_hex, branch_bin);

        // Juntar: Hash Atual (32 bytes) + Ramo (32 bytes)
        memcpy(combined, current_hash, 32);
        memcpy(combined + 32, branch_bin, 32);

        // Novo Hash Duplo
        double_sha256(combined, 64, current_hash);
    }

    // Agora a variável "current_hash" contém o Merkle Root definitivo de 32 bytes!
    ESP_LOGI("STRATUM_PARSER", "Merkle Root calculado com sucesso! (Nível: %d)", branch_count);

    // ... [Seu código anterior do Merkle Root] ...
    ESP_LOGI("STRATUM_PARSER", "Merkle Root calculado com sucesso! (Nível: %d)", branch_count);

    // 5. Montar o Cabeçalho de 80 bytes do Bitcoin
    uint8_t header[80] = {0};

    // Obter os restantes parâmetros do JSON (Versão, nBits, nTime)
    const char *version_hex = cJSON_GetArrayItem(params, 5)->valuestring;
    const char *nbits_hex = cJSON_GetArrayItem(params, 6)->valuestring;
    const char *ntime_hex = cJSON_GetArrayItem(params, 7)->valuestring;

    // Converter as strings HEX para binário e posicionar no cabeçalho
    hex_to_bytes(version_hex, &header[0]);   // 4 bytes: Versão
    hex_to_bytes(prev_hash_hex, &header[4]); // 32 bytes: Bloco Anterior
    memcpy(&header[36], current_hash, 32);   // 32 bytes: Merkle Root (current_hash)
    hex_to_bytes(ntime_hex, &header[68]);    // 4 bytes: Tempo
    hex_to_bytes(nbits_hex, &header[72]);    // 4 bytes: Dificuldade (nBits)
    // Os últimos 4 bytes (76 a 79) são o Nonce. Deixamos a zeros para o ASIC descobrir!

    // 6. Calcular o Midstate (Processamento dos primeiros 64 bytes)
    uint8_t midstate[32] = {0};
    calculate_midstate(header, midstate);

    // 7. Estruturar o Pacote Bitmain BM13xx (SEND_WORK - 70 bytes)
    uint8_t asic_packet[70] = {0};
    asic_packet[0] = 0x55; // Magic Number 1
    asic_packet[1] = 0xAA; // Magic Number 2
    asic_packet[2] = 0x21; // Comando: SEND_WORK
    asic_packet[3] = 0x42; // Comprimento dos dados (Payload)

    // Copiar o Midstate para o pacote
    memcpy(&asic_packet[4], midstate, 32);

    // Copiar os 12 bytes finais do cabeçalho (que não entraram no Midstate)
    // Isso inclui o resto do Merkle Root, nTime e nBits (bytes 64 a 75 do cabeçalho)
    memcpy(&asic_packet[36], &header[64], 12);

    // (Opcional) A arquitetura da Bitmain exige que os bytes sejam invertidos (Little-Endian)
    // Para fins do nosso simulador C3, enviar os dados diretamente já é suficiente para
    // despoletar a interrupção e fazê-lo devolver o Nonce falso.

    // 8. Calcular o CRC5 do pacote
    // O CRC5 é calculado a partir do byte de Comando (byte 2) até ao fim dos dados.
    asic_packet[69] = get_crc5(&asic_packet[2], 67);

    // ... [código anterior] ...
    uart_write_bytes(UART_PORT, asic_packet, 70);
    ESP_LOGI("UART", "=> Pacote SEND_WORK (0x21) de 70 bytes enviado para o ASIC!");

    // --- O GRAN FINALE: SUBMISSÃO DO SHARE ---

    // --- ESCUTA ASSÍNCRONA DO C3 E JULGAMENTO DO HASH ---
    uint8_t asic_resp[32];
    int uart_len = uart_read_bytes(UART_PORT, asic_resp, 11, 10 / portTICK_PERIOD_MS);

    if (uart_len == 11 && asic_resp[0] == 0xAA && asic_resp[1] == 0x55)
    {

        // 1. Pega o Nonce que o C3 (Músculo) enviou
        uint32_t nonce = (asic_resp[4] << 24) | (asic_resp[5] << 16) | (asic_resp[6] << 8) | asic_resp[7];
        ESP_LOGI("CÉREBRO_S3", "Nonce recebido do ASIC: %08lx. Avaliando Target...", (unsigned long)nonce);

        // 2. O S3 refaz o cálculo do Hash! (Injeta o nonce no header e calcula)
        g_current_header[76] = asic_resp[7];
        g_current_header[77] = asic_resp[6];
        g_current_header[78] = asic_resp[5];
        g_current_header[79] = asic_resp[4];

        uint8_t hash1[32], hash2[32];
        mbedtls_sha256(g_current_header, 80, hash1, 0);
        mbedtls_sha256(hash1, 32, hash2, 0);

        // 3. Calcula qual é o alvo exigido pela Pool no momento
        uint8_t target[32];
        calculate_target(g_pool_difficulty, target);

        // 4. Reverte o hash para o formato Big-Endian de leitura humana
        uint8_t hash_rev[32];
        for (int i = 0; i < 32; i++)
            hash_rev[i] = hash2[31 - i];

        // 5. O JULGAMENTO (Hash < Target ?)
        bool is_valid = false;
        for (int i = 0; i < 32; i++)
        {
            if (hash_rev[i] < target[i])
            {
                is_valid = true;
                break;
            } // Bateu a dificuldade!
            if (hash_rev[i] > target[i])
            {
                is_valid = false;
                break;
            } // É pior, rejeita!
        }

        if (is_valid)
        {
            char nonce_hex[9];
            sprintf(nonce_hex, "%08lx", (unsigned long)nonce);
            ESP_LOGW("CÉREBRO_S3", "SHARE APROVADO! Enviando para a Pool...");

            char submit_msg[256];
            snprintf(submit_msg, sizeof(submit_msg),
                     "{\"id\": 4, \"method\": \"mining.submit\", \"params\": [\"%s.%s\", \"%s\", \"00000000\", \"%s\", \"%s\"]}\n",
                     BTC_ADDRESS, WORKER_NAME, g_last_job_id, g_last_ntime, nonce_hex);
            send(sock, submit_msg, strlen(submit_msg), 0);
        }
        else
        {
            ESP_LOGE("CÉREBRO_S3", "Share rejeitado pelo S3 (Abaixo da dificuldade). Poupando você do banimento!");
        }
    }
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
                    if (method)
                    {
                        if (strcmp(method->valuestring, "mining.notify") == 0)
                        {
                            process_mining_notify(cJSON_GetObjectItem(json, "params"), sock);
                        }
                        else if (strcmp(method->valuestring, "mining.set_difficulty") == 0)
                        {
                            cJSON *diff_arr = cJSON_GetObjectItem(json, "params");
                            if (cJSON_IsArray(diff_arr))
                            {
                                g_pool_difficulty = cJSON_GetArrayItem(diff_arr, 0)->valuedouble;
                                ESP_LOGW("STRATUM", "Dificuldade da Pool atualizada: %.3f", g_pool_difficulty);
                            }
                        }
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
    init_uart();
    test_uart_ping_pong();
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