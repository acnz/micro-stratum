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

// --- CONFIGURAÇÕES DE REDE E POOL (Via Menuconfig) ---
#define WIFI_SSID      CONFIG_WIFI_SSID
#define WIFI_PASS      CONFIG_WIFI_PASSWORD
#define BTC_ADDRESS    CONFIG_BTC_ADDRESS

#define POOL_URL       "solo.ckpool.org"
#define POOL_PORT      3333
#define WORKER_NAME    "minis3"

static const char *TAG = "MICRO_STRATUM";

// Handlers para o Wi-Fi
static void wifi_event_handler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data) {
    if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_START) {
        esp_wifi_connect();
    } else if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_DISCONNECTED) {
        esp_wifi_connect();
        ESP_LOGI(TAG, "Tentando reconectar ao Wi-Fi...");
    } else if (event_base == IP_EVENT && event_id == IP_EVENT_STA_GOT_IP) {
        ip_event_got_ip_t* event = (ip_event_got_ip_t*) event_data;
        ESP_LOGI(TAG, "Conectado! IP recebido: " IPSTR, IP2STR(&event->ip_info.ip));
    }
}

// A Tarefa (Thread) que fala com a Pool
static void stratum_client_task(void *pvParameters) {
    char rx_buffer[1024];
    int addr_family = 0;
    int ip_protocol = 0;

    while (1) {
        struct hostent *hp = gethostbyname(POOL_URL);
        if (!hp) {
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
        if (sock < 0) {
            ESP_LOGE(TAG, "Falha ao criar socket TCP");
            break;
        }
        ESP_LOGI(TAG, "Socket criado. Conectando a %s:%d...", POOL_URL, POOL_PORT);

        int err = connect(sock, (struct sockaddr *)&dest_addr, sizeof(struct sockaddr_in));
        if (err != 0) {
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

        // --- LOOP DE ESCUTA (Ouvindo novos trabalhos da rede) ---
        while (1) {
            int len = recv(sock, rx_buffer, sizeof(rx_buffer) - 1, 0);
            if (len < 0) {
                ESP_LOGE(TAG, "Erro na recepção dos dados: errno %d", errno);
                break;
            } else if (len == 0) {
                ESP_LOGW(TAG, "A conexão foi fechada pela Pool.");
                break;
            } else {
                rx_buffer[len] = 0; // Termina a string corretamente
                ESP_LOGI(TAG, "<= RECEBIDO DA POOL:\n%s", rx_buffer);
            }
        }

        if (sock != -1) {
            ESP_LOGE(TAG, "Desligando socket e reiniciando...");
            shutdown(sock, 0);
            close(sock);
        }
    }
    vTaskDelete(NULL);
}

void app_main(void) {
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