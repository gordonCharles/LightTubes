/*
This application is designed to work with a series of 30 APA102 Smart LEDs creating 2.5D animations based on a 
file format defined by the LightTubes.py application.  This application provides read and write file operations as 
pass through operations run over a SmartMesh IP Network to either the flash internal to the LTC5800 or to the external
64Mbit Serial (SPI) flash.  LightTube palettes, the values for all of the LEDs for a single transition are stored in 
external flash, one palette for every 256 byte page.  While each palette is 4 bytes/LED * 30 LEDs = 120 bytes; having
a palette per page allows for simple erasing and rewriting of a single palette.  The sequences of transition types and 
corresponging LightTube palettes are stored as "songs" in the LTC5800's internal flash.  During performances, once the 
application receives a PKT_SET_START_TIME packet, which includes the song selection, the application waits unti the set 
start time and then begins "playing the song" by reading the transitions for the song, loading the LightTube palettes 
encoded in the song and performing the math functions to determine the LED light values from the previous and next 
LightTube palettes based on the transition type.  The application uses a delay lock loop with a 5ms epoch to lock the 
timing of the playback to the network clock, ensureing lockstep operation for multiple instances of this application 
each running on a separate LTC5800.  

Following power on / reset the application joins the network and waits for one of a series of network commands which
will instruct the application to do one of the following:

1) Erase the external flash
2) Write to the external flash
3) Read from the external flash
4) Erase a particular song (piece) from the internal flash
5) Append to a particular song (piece) in the internal flash
6) Load a starting color palette from external flash into the LEDs
7) Read a song from internal flash and send it over the network to the LightTubes.py application via the network manager

*/

// C includes
#include "string.h"
#include "stdio.h"

// SDK includes
#include "dn_common.h"
#include "dnm_local.h"
#include "dn_time.h"
#include "dn_system.h"
#include "dn_api_param.h"
#include "dn_fs.h"
#include "well_known_ports.h"
#include "cli_task.h"
#include "loc_task.h"
#include "dn_exe_hdr.h"
#include "Ver.h"
#include "dn_spi.h"
#include "dn_gpio.h"
#include "app_task_cfg.h"


// project includes
#include "app_task_cfg.h"

//=========================== defines =========================================
#define SYNCTEMP_UDP_PORT          WKP_USER_3
#define LED_APP_PORT               0xF0BA

#define APP_CONFIG_FILENAME        "2syncBlk.cfg"
#define DEFAULT_RPT_PERIOD         3600             // seconds
#define APP_MAGIC_NUMBER           0x73797470       // 'sytp'
#define MAX_RX_PAYLOAD             90
//=========================== Join defines ====================================
#define HI_DUTY            255
#define LOW_DUTY           5
#define HI_TIMEOUT         15 * SECOND   // 2x average sync time at 100%, so if a manager is in range we'll likely hear it
#define LOW_TIMEOUT        150 * SECOND  // Average sync time to manager at 5%
#define IDLE_TIMEOUT       30 * SECOND   // If we don't hear at either two, might want to wait a lot longer
//=========================== variables =======================================

// command identifiers

#define CMDID_GET                  0x01
#define CMDID_SET                  0x02
#define CMDID_RESPONSE             0x03
#define CMDID_TEMP_DATA            0x04

#define PKT_SET_START_TIME         0x01
#define PKT_EXTERNAL_FLASH_ERASE   0x02
#define PKT_EXTERNAL_FLASH_WRITE   0x03
#define PKT_SONG_ERASE             0x04
#define PKT_SONG_APPEND            0x05
#define PKT_STOP                   0x06
#define PKT_SEND_SONG              0x07
#define PKT_SEND_SCENE             0x08
#define PKT_SEND_SHIFT             0x09
#define PKT_ENABLE_INIT_COLOR      0x0A
#define PKT_TURN_TO_BLACK          0x0B
#define PKT_EXTERNAL_FLASH_READ    0x0C
#define PKT_SONG_READ              0x0D
#define PKT_COM_COUNT_RESET        0x0E

// response codes

#define APP_RC_OK                  0x00
#define APP_RC_ERR                 0x01
#define LED_ACK                    0x01
#define LED_NAK                    0x02

//=============== LED Control =================================================
#define LED_STRING_LENGTH          31
#define NUM_PIXELS                 LED_STRING_LENGTH // extra pixel to handle shifting.
#define FLICKER                    0
#define RED                        1
#define GREEN                      2
#define BLUE                       3
#define NUM_COMPS                  4    // Number of Color Components - Flicker, Red, Green, Blue
#define NUM_STRINGS                2
#define SPI_BUFFER_LENGTH          4*LED_STRING_LENGTH + 4 // +4 for first four empty bytes
#define APP_DATA_BUF_SIZE          SPI_BUFFER_LENGTH
#define PERIOD_DEFAULT             1000
#define PERIOD                     10

//=============== serial flash commands =======================================
#define READ_DEVICE_ID             0x90
#define CHIP_ERASE                 0x60
#define SECTOR_ERASE               0x20
#define BLOCK_ERASE                0xD8
#define PAGE_PROGRAM               0x02
#define WRITE_ENABLE               0x06
#define READ_DATA                  0x03
#define FAST_READ                  0x0B
#define READ_STATUS1               0x05
#define READ_STATUS2               0x35
#define READ_STATUS3               0x33

#define BUSY_MASK                  0x01

#define FLASH_ERASED               0x01
#define FLASH_WRITTEN              0x02

#define SHIFT_BASE                 (1 << 22)

//=============== internal flash ==============================================
const char * const songLookup[] = {
"2song1.dat", 
"2song2.dat", 
"2song3.dat", 
"2song4.dat", 
"2song5.dat", 
"2song6.dat",
"2song7.dat", 
"2song8.dat", 
"2song9.dat", 
"2song10.dat", 
"2song11.dat", 
"2song12.dat" 
};

//=============== song types =======================================
#define INIT                      0xFF
#define END                       0xFE
#define SHIFT                     0xF0
//#define SHIFT_LEFT                0xF1
#define LINEAR_FADE               0x01
#define EXPONENTIAL_FADE          0x02
#define INV_EXPONENTIAL_FADE      0x03
#define SWIPE_DOWN                0x04
#define SWIPE_UP                  0x05


INT8U Rand(INT8U component) {
static const INT8U lookup[256] =
{
0xFCU, 0xAAU, 0x4FU, 0xF0U, 0xFBU, 0x1AU, 0x89U, 0xC6U, 
0xF2U, 0x6EU, 0x93U, 0x09U, 0xD0U, 0x4AU, 0xE8U, 0xE2U, 
0xD8U, 0xC9U, 0xF3U, 0xA3U, 0x62U, 0xCFU, 0xA1U, 0xDAU, 
0x38U, 0xEFU, 0xBDU, 0xACU, 0x9FU, 0x2CU, 0xBFU, 0x99U, 
0x2BU, 0x75U, 0xFDU, 0xF4U, 0xA5U, 0xE3U, 0x9DU, 0xE2U, 
0xF6U, 0xF8U, 0xFCU, 0xFDU, 0xD3U, 0xF8U, 0x6BU, 0x75U, 
0xFDU, 0xB2U, 0xF5U, 0xC5U, 0xA3U, 0x2DU, 0xCEU, 0xEEU, 
0xAAU, 0x98U, 0x25U, 0xE7U, 0x68U, 0xC9U, 0xB8U, 0xFBU, 
0xFCU, 0xFEU, 0xEDU, 0x14U, 0x61U, 0xB9U, 0xEEU, 0x4AU, 
0xDDU, 0xC0U, 0xC0U, 0xFEU, 0xECU, 0xEAU, 0xC7U, 0x91U, 
0xC8U, 0x33U, 0xCEU, 0x96U, 0x95U, 0xFAU, 0x41U, 0xD6U, 
0xD3U, 0xC2U, 0x46U, 0xFEU, 0xFEU, 0xADU, 0x83U, 0x55U, 
0xFEU, 0xA4U, 0xE5U, 0xFBU, 0xD8U, 0x2CU, 0xC0U, 0xFEU, 
0xE6U, 0xF3U, 0x92U, 0x55U, 0xE2U, 0xE8U, 0xD4U, 0x4BU, 
0x5DU, 0xF5U, 0xE8U, 0x60U, 0x26U, 0xECU, 0xFCU, 0x7EU, 
0xC7U, 0xFEU, 0x09U, 0xEBU, 0x43U, 0x68U, 0xB0U, 0x85U, 
0xD4U, 0xFDU, 0xEEU, 0xFEU, 0xFDU, 0x03U, 0xD9U, 0xF5U, 
0xA8U, 0xC9U, 0xD0U, 0x54U, 0xFCU, 0xFAU, 0xFEU, 0x97U, 
0x1EU, 0x3FU, 0xCEU, 0xFDU, 0xACU, 0x9FU, 0x64U, 0xE6U, 
0xFDU, 0xEAU, 0x94U, 0xCDU, 0x12U, 0xD6U, 0xFEU, 0x59U, 
0xD3U, 0xBAU, 0xE7U, 0x1EU, 0xF4U, 0xD8U, 0xE2U, 0xF9U, 
0x1BU, 0x91U, 0xF6U, 0xE7U, 0xF5U, 0xFCU, 0xE4U, 0xF2U, 
0x8DU, 0xFEU, 0x52U, 0x7EU, 0x78U, 0xC5U, 0xABU, 0xFEU, 
0xD5U, 0xEBU, 0xF4U, 0x24U, 0x98U, 0x33U, 0xF5U, 0xF1U, 
0xFAU, 0xFEU, 0xF9U, 0xE4U, 0x05U, 0x29U, 0xF9U, 0x52U, 
0x1DU, 0xF9U, 0x55U, 0xC5U, 0x97U, 0x37U, 0x9FU, 0xFEU, 
0xD1U, 0xFEU, 0x48U, 0xE6U, 0xE2U, 0x5CU, 0xFAU, 0xFBU, 
0xE8U, 0xE2U, 0xEFU, 0x33U, 0xF1U, 0xF3U, 0xEAU, 0x59U, 
0xF3U, 0xD8U, 0x14U, 0xFCU, 0xE8U, 0xFDU, 0x73U, 0xE5U, 
0x38U, 0x4AU, 0xDDU, 0xFEU, 0x58U, 0xC4U, 0xEEU, 0x24U, 
0x8EU, 0xDDU, 0x89U, 0x63U, 0xEDU, 0xFEU, 0xDFU, 0x02U, 
0xFDU, 0xD8U, 0x81U, 0xF8U, 0x12U, 0xEDU, 0x92U, 0x78U, 
};
return lookup[component];
};
// 
//=========================== structures =====================================
typedef struct {
   OS_EVENT*       joinedSem;
   OS_STK          joinTaskStack[TASK_APP_JOIN_STK_SIZE];
} join_app_vars_t;

join_app_vars_t join_app_vars;

typedef struct {
   INT8U                     comp[NUM_STRINGS][NUM_PIXELS][NUM_COMPS];
} LEDString_t;

typedef struct {
   INT32S                    comp[NUM_PIXELS][NUM_COMPS];
} pixelDelta_t;

typedef struct {
   INT8U                     comp[NUM_COMPS];
} pixel_t;

enum transitionType {
   LINEAR,
   EXPONENTIAL,
   LOGARITHMIC
};

//=== packet formats

PACKED_START

typedef struct{
   INT32U magic_number;      // APP_MAGIC_NUMBER, big endian
   INT8U  cmdId;             // command identifier
   INT8U  payload[];         // payload
} app_payload_ht;

typedef struct{
   INT8U  cmdId;             // command identifier
   INT8U  payload[];         // payload
} led_payload_ht;

typedef struct {
   INT32U                    offset;
   INT32U                    S;
   INT32U                    uS;
} time_t;

PACKED_STOP

//=== file formats

PACKED_START

typedef struct{
   INT8U type;              // type of sequence
   INT8U stop;              // stop postion - for wipes only
   INT16U index;            // scene reference
} seq_header_t;

typedef struct{
   INT16U duration;          // transition duration
   INT16U backPorch;         // back porch duration
} scene_t;

typedef struct{
//   INT16U duration;          // transition duration
//   INT16U backPorch;         // back porch duration
   INT16U frontPorch;
   INT16U length;
   INT16U startPhase;
   INT16U endPhase;
} shift_t;

PACKED_STOP


// 
//=========================== variables =======================================

/// variables local to this application
typedef struct {
   OS_STK                    spiTaskStack[TASK_APP_SPI_STK_SIZE];
   INT8U                     spiTxBuffer[SPI_BUFFER_LENGTH];
   INT8U                     spiRxBuffer[SPI_BUFFER_LENGTH];
   OS_EVENT*                 joinedSem;
   INT16U                    period;        ///< period (in ms) between transmissions
} spiNetApp_vars_t;

pixelDelta_t              current;
pixelDelta_t              flicker;
pixelDelta_t              flickerCurr;
pixelDelta_t              delta;
LEDString_t               startEnd; // Use an array of two strings and switch back and forth instead of copying end value to start

dn_spi_open_args_t        spiOpenArgs;
dn_ioctl_spi_transfer_t   spiTransfer;


spiNetApp_vars_t          spiNetApp_vars;
INT32U*                   spiTxBuf32;// = (INT32U *)spiNetApp_vars.spiTxBuffer[0];

time_t                    startTime;

dn_time_asn_t             currentASN;
dn_time_utc_t             currentUTC;
INT8U                     song;
INT32U                    songTime;
OS_EVENT*                 startSong;                   ///< posted when a start of Song has been received
INT8U                     stopSong;              
INT8U                     songPlaying;     
OS_EVENT*                 fakeJoin;  


//=== contents of configuration file

typedef struct{
   INT32U reportPeriod;      // report period, in seconds
} app_cfg_t;

//=========================== variables =======================================

typedef struct {
   // tasks
   OS_STK               sampleTaskStack[TASK_APP_SAMPLE_STK_SIZE];
   OS_TMR*              sampleTaskStackTimer;
   OS_EVENT*            sampleTaskStackTimerSem;      ///< posted when sampleTaskStackTimer expires
   OS_STK               processRxTaskStack[TASK_APP_PROCESSRX_STK_SIZE];
   // network
   OS_EVENT*            joinedSem;                    ///< posted when stack has joined
   INT8U                isJoined;                     ///< 0x01 if the mote has joined the network, 0x00 otherwise
   // configuration
   OS_EVENT*            dataLock;                     ///< locks shared resources
   app_cfg_t            app_cfg;                      ///< structure containing the application's configuration
   INT64S               nextReportUTCSec;             ///< time next report is scheduled
   // rx packet
   OS_EVENT*            rxPkLock;                     ///< locks received packet information
   dn_ipv6_addr_t       rxPkSrc;                      ///< IPv6 address of the sender
   INT8U                rxPkPayload[MAX_RX_PAYLOAD];  ///< received payload
   INT8U                rxPkPayloadLen;               ///< number of bytes in the received payload
   OS_EVENT*            rxPkReady;                    ///< posted when an rx packet is ready for consumption
} synctemp_app_vars_t;

synctemp_app_vars_t synctemp_v;

//=========================== prototypes ======================================

//=== CLI handlers
dn_error_t cli_getPeriod(const char* arg, INT32U len);
dn_error_t cli_setPeriod(const char* arg, INT32U len);

//=== tasks
static void sampleTask(void* unused);
void   sampleTaskStackTimer_cb(void* pTimer, void *pArgs);
static void processRxTask(void* unused);
static void joinTask(void* unused);

//=== helpers

// network
dn_error_t rxNotif(dn_api_loc_notif_received_t* rxFrame, INT8U length);

// formatting
void printf_buffer(INT8U* buf, INT8U len);

// configuration
void setPeriod(INT32U reportPeriod);

// configuration file
void loadConfigFile();
void syncToConfigFile();

// lock
void lockData();
void unlockData();
void lockRxPk();
void unlockRxPk();

//=========================== const ===========================================

const dnm_ucli_cmdDef_t cliCmdDefs[] = {
   {&cli_getPeriod,      "getperiod",    "getperiod",              DN_CLI_ACCESS_LOGIN},
   {&cli_setPeriod,      "setperiod",    "setperiod <period>",     DN_CLI_ACCESS_LOGIN},
   {NULL,                 NULL,          NULL,                     DN_CLI_ACCESS_NONE},
};

//=========================== initialization ==================================

/**
\brief This is the entry point for the application code.
*/
int p2_init(void) {
   INT8U           osErr;
   
   // clear module variables
   memset(&synctemp_v,0,sizeof(synctemp_app_vars_t));
   
   // the mote is not joined
   synctemp_v.isJoined = 0x00;
   
   // semaphores
   
   synctemp_v.sampleTaskStackTimerSem = OSSemCreate(0);    // NOT expired by default
   ASSERT(synctemp_v.sampleTaskStackTimerSem!=NULL);
   
   synctemp_v.joinedSem = OSSemCreate(0);                  // NOT joined by default
   ASSERT(synctemp_v.joinedSem!=NULL);
   
   fakeJoin = OSSemCreate(0);                  // NOT joined by default
   ASSERT(fakeJoin!=NULL);
   
   synctemp_v.dataLock = OSSemCreate(1);                   // data unlocked by default
   ASSERT(synctemp_v.dataLock!=NULL);
   
   synctemp_v.rxPkLock = OSSemCreate(1);                    // rx packet unlocked by default
   ASSERT(synctemp_v.rxPkLock!=NULL);
   
   synctemp_v.rxPkReady = OSSemCreate(0);                   // rx packet NOT ready by default
   ASSERT(synctemp_v.rxPkReady!=NULL);
   
   startSong = OSSemCreate(0);                              // start song off by default
   ASSERT(startSong!=NULL);
      
   //===== register a callback to receive packets
   
   dnm_loc_registerRxNotifCallback(rxNotif);
   
   //===== initialize helper tasks
   
   cli_task_init(
      "synctemp",                    // appName
      cliCmdDefs                     // cliCmds
   );
   
   loc_task_init(
      JOIN_NO,                       // fJoin
      NETID_NONE,                    // netId
      SYNCTEMP_UDP_PORT,             // udpPort
      synctemp_v.joinedSem,          // joinedSem
      500,                           // bandwidth set to 500 ms (14 tubes = 28 packets/s)  Note: BANDWIDTH_NONE = use default BW (set at manager)
      NULL                           // serviceSem
   );
   
   //===== initialize tasks (and timer)
   
   //===== initialize joinTask  
   osErr = OSTaskCreateExt(
      joinTask,
      (void *) 0,
      (OS_STK*) (&join_app_vars.joinTaskStack[TASK_APP_JOIN_STK_SIZE - 1]),
      TASK_APP_JOIN_PRIORITY,
      TASK_APP_JOIN_PRIORITY,
      (OS_STK*) join_app_vars.joinTaskStack,
      TASK_APP_JOIN_STK_SIZE,
      (void *) 0,
      OS_TASK_OPT_STK_CHK | OS_TASK_OPT_STK_CLR
   );
   ASSERT(osErr==OS_ERR_NONE);
   OSTaskNameSet(TASK_APP_JOIN_PRIORITY, (INT8U*)TASK_APP_JOIN_NAME, &osErr);
   ASSERT(osErr==OS_ERR_NONE);
   
   // sampleTask
   osErr = OSTaskCreateExt(
      sampleTask,
      (void *) 0,
      (OS_STK*) (&synctemp_v.sampleTaskStack[TASK_APP_SAMPLE_STK_SIZE - 1]),
      TASK_APP_SAMPLE_PRIORITY,
      TASK_APP_SAMPLE_PRIORITY,
      (OS_STK*) synctemp_v.sampleTaskStack,
      TASK_APP_SAMPLE_STK_SIZE,
      (void *) 0,
      OS_TASK_OPT_STK_CHK | OS_TASK_OPT_STK_CLR
   );
   ASSERT(osErr==OS_ERR_NONE);
   OSTaskNameSet(TASK_APP_SAMPLE_PRIORITY, (INT8U*)TASK_APP_SAMPLE_NAME, &osErr);
   ASSERT(osErr==OS_ERR_NONE);
   
   // sampleTask Timer
   synctemp_v.sampleTaskStackTimer = OSTmrCreate(
      DEFAULT_RPT_PERIOD,                        // dly
      DEFAULT_RPT_PERIOD,                        // period
      OS_TMR_OPT_ONE_SHOT,                       // opt
      (OS_TMR_CALLBACK)&sampleTaskStackTimer_cb, // callback
      NULL,                                      // callback_arg
      NULL,                                      // pname
      &osErr                                     // perr
   );
   ASSERT(osErr==OS_ERR_NONE);
   
   // processRxTask
   osErr = OSTaskCreateExt(
      processRxTask,
      (void *) 0,
      (OS_STK*) (&synctemp_v.processRxTaskStack[TASK_APP_PROCESSRX_STK_SIZE - 1]),
      TASK_APP_PROCESSRX_PRIORITY,
      TASK_APP_PROCESSRX_PRIORITY,
      (OS_STK*) synctemp_v.processRxTaskStack,
      TASK_APP_PROCESSRX_STK_SIZE,
      (void *) 0,
      OS_TASK_OPT_STK_CHK | OS_TASK_OPT_STK_CLR
   );
   ASSERT(osErr==OS_ERR_NONE);
   OSTaskNameSet(TASK_APP_PROCESSRX_PRIORITY, (INT8U*)TASK_APP_PROCESSRX_NAME, &osErr);
   ASSERT(osErr==OS_ERR_NONE);
   
   return 0;
}

//=========================== Join Task ====================================

static void joinTask(void* unused) {
   dn_error_t      dnErr;
   INT8U           osErr;
   INT8U           joinDC;
   INT8U           rc;
   INT8U           fJoined = FALSE;
   INT8U           routingMode = 1;      // 0 = routing, 1= non-routing
   
   // Give stack time to print banner
   OSTimeDly(1 * SECOND);
   
   while (1) { // this is a task, it executes forever
      
      if(!fJoined){
         joinDC = HI_DUTY;
         dnErr = dnm_loc_setParameterCmd(
                              DN_API_PARAM_JOINDUTYCYCLE,   // parameter
                              &joinDC,                      // payload (parameter value)
                              sizeof(INT8U),                // length
                              &rc                           // rc
         );
         ASSERT(dnErr == DN_ERR_NONE);
         ASSERT(rc == DN_API_RC_OK);

         dnErr = dnm_loc_setParameterCmd(
                              DN_API_PARAM_ROUTINGMODE,     // parameter
                              &routingMode,                 // payload (parameter value)
                              sizeof(INT8U),                // length
                              &rc                           // rc
         );
         ASSERT(dnErr == DN_ERR_NONE);
         ASSERT(rc == DN_API_RC_OK);
             
         dnErr = dnm_loc_joinCmd(&rc);
         ASSERT(dnErr == DN_ERR_NONE);
         ASSERT(rc == DN_API_RC_OK);
         
         // wait for the loc_task to finish joining the network with a timeout
         OSSemPend(synctemp_v.joinedSem, HI_TIMEOUT, &osErr);
         // We only expect OSSemPend to return OS_ERR_NONE or OS_ERR_TIMEOUT
         if(osErr==OS_ERR_NONE){
            fJoined = TRUE;
            osErr = OSSemPost(fakeJoin);
            ASSERT(osErr == OS_ERR_NONE);
         }     
      } else {
         OSTimeDly(90 * SECOND);
      }
   }
}

//=========================== CLI handlers ====================================

dn_error_t cli_getPeriod(const char* arg, INT32U len) {
   INT8U           isJoined;
   INT64S          nextReportUTCSec;
   dn_time_asn_t   currentASN;
   dn_time_utc_t   currentUTC;
   INT32U          timeToNext;
   
   // print current configuration
   dnm_ucli_printf(
      "Current configuration: reportPeriod = %u seconds\r\n",
      synctemp_v.app_cfg.reportPeriod
   );
   
   // retrieve what I need
   lockData();
   isJoined             = synctemp_v.isJoined;
   nextReportUTCSec     = synctemp_v.nextReportUTCSec;
   unlockData();
   
   // print next transmission time
   if (isJoined==0x01) {
      
      // get current time
      dn_getNetworkTime(
         &currentASN,
         &currentUTC
      );
      
      // calculate timeToNext
      timeToNext = (INT32U)nextReportUTCSec - (INT32U)currentUTC.sec;
      
      // print timeToNext
      dnm_ucli_printf(
         "Next trigger in %d seconds\r\n",
         timeToNext
      );
   }
   
   return DN_ERR_NONE;
}

dn_error_t cli_setPeriod(const char* arg, INT32U len) {
   INT32U     newReportPeriod;
   int        l;
   
   //--- param 0: a
   l = sscanf(arg, "%u", &newReportPeriod);
   if (l < 1) {
      return DN_ERR_INVALID;
   }
   
   // set the period
   setPeriod(newReportPeriod);
  
   return DN_ERR_NONE;
}

//===== External Flash
void serialFlashWriteEnable(dn_ioctl_spi_transfer_t spiTransfer, dn_error_t dnErr) {

   spiTransfer.transactionLen     = 1;
   spiTransfer.slaveSelect        = DN_SPIM_SS_1n;
   spiNetApp_vars.spiTxBuffer[0]  = WRITE_ENABLE;
      
   dnErr = dn_ioctl(
      DN_SPI_DEV_ID,
      DN_IOCTL_SPI_TRANSFER,
      &spiTransfer,
      sizeof(spiTransfer)
   );
   ASSERT(dnErr >= DN_ERR_NONE);
      
}

void serialFlashErase(INT32U sector, dn_ioctl_spi_transfer_t spiTransfer, dn_error_t dnErr) {
   INT8U                    busyStatus;
   INT32U                   time;
   INT8U                    comp;

   dnm_ucli_printf("Starting Flash Erase:\r\n");         

   time = 0;
   spiTransfer.transactionLen     = 1;
   spiTransfer.slaveSelect        = DN_SPIM_SS_1n;
   spiTransfer.rxBufferLen        = sizeof(spiNetApp_vars.spiRxBuffer);
   spiNetApp_vars.spiTxBuffer[0]  = CHIP_ERASE;

   dnErr = dn_ioctl(
      DN_SPI_DEV_ID,
      DN_IOCTL_SPI_TRANSFER,
      &spiTransfer,
      sizeof(spiTransfer)
   );
   ASSERT(dnErr >= DN_ERR_NONE);
   
   spiTransfer.transactionLen     = 4;
   spiNetApp_vars.spiTxBuffer[0]  = READ_STATUS1;
   do {
      OSTimeDly(1000);
      time += 1;
      
      dnErr = dn_ioctl(
         DN_SPI_DEV_ID,
         DN_IOCTL_SPI_TRANSFER,
         &spiTransfer,
         sizeof(spiTransfer)
      );
      ASSERT(dnErr >= DN_ERR_NONE);

      busyStatus = spiNetApp_vars.spiRxBuffer[1] & BUSY_MASK;
      dnm_ucli_printf(".");                       
      
   } while (busyStatus > 0);
   dnm_ucli_printf("\r\nFlash Erase Complete after %d seconds\r\n", time);               

}

INT16U serialFlashReadDevID(dn_ioctl_spi_transfer_t spiTransfer, dn_error_t dnErr) {
   INT16U         deviceID;

   spiTransfer.transactionLen     = 6;
   spiTransfer.slaveSelect        = DN_SPIM_SS_1n;
   spiTransfer.rxBufferLen        = sizeof(spiNetApp_vars.spiRxBuffer);
   spiNetApp_vars.spiTxBuffer[0]  = READ_DEVICE_ID;

   dnErr = dn_ioctl(
      DN_SPI_DEV_ID,
      DN_IOCTL_SPI_TRANSFER,
      &spiTransfer,
      sizeof(spiTransfer)
   );
   ASSERT(dnErr >= DN_ERR_NONE);
   
   deviceID = ((INT16U) spiNetApp_vars.spiRxBuffer[4] << 8) + (INT16U) spiNetApp_vars.spiRxBuffer[5];
   return deviceID;
      
}

void serialFlashReadStatus(dn_ioctl_spi_transfer_t spiTransfer, dn_error_t dnErr) {
   INT8U                     status[2];
   
   spiTransfer.transactionLen     = 2;
   spiTransfer.slaveSelect        = DN_SPIM_SS_1n;
   spiTransfer.rxBufferLen        = sizeof(spiNetApp_vars.spiRxBuffer);
   spiNetApp_vars.spiTxBuffer[0]  = READ_STATUS1;

   dnErr = dn_ioctl(
      DN_SPI_DEV_ID,
      DN_IOCTL_SPI_TRANSFER,
      &spiTransfer,
      sizeof(spiTransfer)
   );
   ASSERT(dnErr >= DN_ERR_NONE);
   
   status[0] = spiNetApp_vars.spiRxBuffer[1];
   
   spiNetApp_vars.spiTxBuffer[0]  = READ_STATUS2;

   dnErr = dn_ioctl(
      DN_SPI_DEV_ID,
      DN_IOCTL_SPI_TRANSFER,
      &spiTransfer,
      sizeof(spiTransfer)
   );
   ASSERT(dnErr >= DN_ERR_NONE);
   
   status[1] = spiNetApp_vars.spiRxBuffer[1];
   
   spiNetApp_vars.spiTxBuffer[0]  = READ_STATUS2;

   dnErr = dn_ioctl(
      DN_SPI_DEV_ID,
      DN_IOCTL_SPI_TRANSFER,
      &spiTransfer,
      sizeof(spiTransfer)
   );
   ASSERT(dnErr >= DN_ERR_NONE);
   
   status[2] = spiNetApp_vars.spiRxBuffer[1];
      
   //dnm_ucli_printf("Status: %x %x %x\r\n", status[0], status[1], status[2]);         
      
}

void serialFlashProgram(dn_ioctl_spi_transfer_t spiTransfer, dn_error_t dnErr) {

   spiTransfer.slaveSelect        = DN_SPIM_SS_1n;
   spiTransfer.rxBufferLen        = sizeof(spiNetApp_vars.spiRxBuffer);
   spiNetApp_vars.spiTxBuffer[0]  = PAGE_PROGRAM;
      
   dnErr = dn_ioctl(
      DN_SPI_DEV_ID,
      DN_IOCTL_SPI_TRANSFER,
      &spiTransfer,
      sizeof(spiTransfer)
   );
   ASSERT(dnErr >= DN_ERR_NONE);
   OSTimeDly(3);   
}

void serialFlashReadData(dn_ioctl_spi_transfer_t spiTransfer, dn_error_t dnErr) {

   spiTransfer.slaveSelect        = DN_SPIM_SS_1n;
   spiNetApp_vars.spiTxBuffer[0]  = READ_DATA;
   dnErr = dn_ioctl(
      DN_SPI_DEV_ID,
      DN_IOCTL_SPI_TRANSFER,
      &spiTransfer,
      sizeof(spiTransfer)
   );
   ASSERT(dnErr >= DN_ERR_NONE);
}

dn_error_t cli_displayFS() {
   dn_fs_fsinfo_t       info;
   dn_error_t           dnErr;
   
   dnErr = dn_fs_getFSInfo(&info);
   ASSERT(dnErr == DN_ERR_NONE);
   
   dnm_ucli_printf("shortPageSize  = %d\r\n", info.shortPageSize);
   dnm_ucli_printf("longPageSize   = %d\r\n", info.longPageSize);
   dnm_ucli_printf("numOfPagesUsed = %d\r\n", info.numOfPagesUsed);
   dnm_ucli_printf("maxNumOfPages  = %d\r\n", info.maxNumOfPages);
   dnm_ucli_printf("numOfFilesUsed = %d\r\n", info.numOfFilesUsed);
   dnm_ucli_printf("maxNumOfFiles  = %d\r\n", info.maxNumOfFiles);
   
   return DN_ERR_NONE;
}

dn_error_t cli_listFiles() {
   dn_error_t           dnErr;
   dn_fs_handle_t       fileHandle;
   INT32S               index;
   dn_fs_fileinfo_t    fileInfo;
   
   dnErr = dn_fs_getFileInfo(
      fileHandle,
      &fileInfo
   );
   
   for (index=0; index <32; index++) {
      fileHandle = dn_fs_findByIdx(index);
      if (fileHandle >= 0) {
         dnErr = dn_fs_getFileInfo(
            fileHandle,
            &fileInfo
         );
         dnm_ucli_printf("File : %s    Length: %d\r\n", fileInfo.name, fileInfo.len);
      }
   }   
   return DN_ERR_NONE;
}

void eraseFile(char* fileName) {
   dn_error_t          dnErr;
   
   dnErr = dn_fs_delete(fileName);
         switch (dnErr){
         case DN_ERR_NOT_FOUND:
            dnm_ucli_printf("Error: file not found\r\n");
         break;
         case DN_ERR_CORRUPTED:
            dnm_ucli_printf("Error: corrupt filesystem\r\n");
         break;
         case DN_ERR_ERROR:
            dnm_ucli_printf("Error: other\r\n");
         break;
         case DN_ERR_NONE:
            dnm_ucli_printf("%s Erased\r\n", fileName);
         break;
      }
}

 dn_fs_handle_t openFile(char* fileName) {
   dn_error_t          dnErr;
   dn_fs_handle_t      fileHandle;
   INT8U               offset;
   
   // open file
   fileHandle = dn_fs_open(
      fileName,
      DN_FS_OPT_CREATE,     // DN_FS_OPT_CREATE will create the file if it does not already exist
      4096,                 // Any value larger than 2048 results in the file being defined as multipage
      DN_FS_MODE_SHADOW
   );
   ASSERT(fileHandle >= 0);

   return fileHandle;
}

void appendFile(dn_fs_handle_t fileHandle, const INT8U* data, INT32U length) {
   dn_error_t          dnErr;
   dn_fs_fileinfo_t    fileInfo;
   INT32U              offset;
   
   dnErr = dn_fs_getFileInfo(
      fileHandle,
      &fileInfo
   );
   ASSERT(dnErr >= 0);
   offset = fileInfo.len;
   // write file
   dnErr = dn_fs_write(
      fileHandle,
      offset, 
      data,
      length
   );
   ASSERT(dnErr >= 0);
}

void readFile(dn_fs_handle_t fileHandle, INT8U* data, INT32U offset, INT32U length) {
   dn_error_t          dnErr;
   dn_fs_fileinfo_t    fileInfo;

   // get current file length (in bytes)
   dnErr = dn_fs_getFileInfo(
      fileHandle,
      &fileInfo
   );
   ASSERT(dnErr >= 0);

   if (offset + length > fileInfo.len) {
      dnm_ucli_printf("ERROR attempting to read past the end (Byte : %d) of filename %s\r\n", fileInfo.len, fileInfo.name);
   } else {
      dnErr = dn_fs_read(
      fileHandle,
      offset, // offset
      data,
      length
      );
   }
   ASSERT(dnErr >= 0);
}

void loadLEDs(dn_ioctl_spi_transfer_t spiTransfer, dn_error_t dnErr) {
   
      spiTransfer.transactionLen     = 128;
      spiTransfer.slaveSelect        = DN_SPIM_SS_0n;
      dnErr = dn_ioctl(
         DN_SPI_DEV_ID,
         DN_IOCTL_SPI_TRANSFER,
         &spiTransfer,
         sizeof(spiTransfer)
      );
      ASSERT(dnErr >= DN_ERR_NONE);
}

//=========================== tasks ===========================================

static void sampleTask(void* unused) {
   INT8U                osErr;
   INT8U                dnErr;
   dn_time_asn_t        currentASN;
   dn_time_utc_t        currentUTC;
   INT8U                numBytesRead;
   INT16S               temperature;
   INT32U               reportRateMs;
   INT64U               timeToWaitMs;
   INT8U                spkBuf[sizeof(loc_sendtoNW_t) + sizeof(app_payload_ht) + sizeof(INT16U)];
   loc_sendtoNW_t*      spkToSend;
   app_payload_ht*      spayloadToSend;
   INT8U                src;
   INT8U                i,k;
   dn_fs_handle_t       readFileHandle;
   dn_fs_fileinfo_t     readFileInfo;
   INT32U               readBufferPtr;
   seq_header_t         seqHdr;
   scene_t              scene;
   shift_t              shift;
   INT16U               currentIndex;
   INT8U                pixel;
   INT32U               position;
   INT8U                comp;
   INT8U                newSequence;
   INT8U                loadSequence;
   INT8U                start;
   INT8U                end;
   INT8U                holdStart;
   INT8U                rightShift;
   INT32U               positionDelta;
   INT32U               fractionalPosition;
   INT32U               remainingPosition;
   INT64U               nextLEDLoadTime;
   INT64U               UTC64;
   INT16U               backPorch;
   INT16U               transitionCount;
   INT8U                startBackPorch;
   INT16U               wholePosition;
   INT16U               oldWholePosition;
   INT8U                readBuf[8];   
   INT32U               flashAddress;
   INT32U               numSkips;
   INT32U               minWait;
   INT8U                swipeStart;
   INT8U                lastSeqSwipe;
   INT32U               debugInt32U;
   INT8U                flickerPhase;
   INT8U                flickerOn;
   INT8U                flickerOnNext;
   INT16U               pixFlickerPhase;
   INT8U                flickerSpeed;
   INT8U                flickerDiv;
   INT16U               commandCount;
   
   while (1) { // this is a task, it executes forever
         
     
      OSSemPend(startSong, 0, &osErr);
      songPlaying   = 1;
      stopSong      = 0;
      songTime      = 0;
      readBufferPtr = 0;
      newSequence   = 1;
      loadSequence  = 0;
      start         = 0;
      end           = 1;
      rightShift    = 1;
      nextLEDLoadTime = ((INT64U) startTime.S)*1000 + ((INT64U) startTime.uS + 500)/1000;
      numSkips      = 0;
      minWait       = 10000;
      backPorch     = 0;
      swipeStart    = 0;
      lastSeqSwipe  = 0;
      flickerPhase  = 0;
      flickerOn     = 0;
      flickerOnNext = 0;
      pixFlickerPhase = 0;
      flickerDiv     = 0;
      commandCount = 0;

      while (stopSong == 0) { // Repeat loop until stopSong = 0
      

      readFileHandle = openFile((char *)songLookup[song]);
      dnErr = dn_fs_getFileInfo(
         readFileHandle,
         &readFileInfo
      );
      ASSERT(dnErr >= 0);
      while ((readFileInfo.len - readBufferPtr) > 0) {
        if ((readFileInfo.len - readBufferPtr) < 1) {
          stopSong = 1;
          break;  // Reached end of song file
        }

        // Fast forward to begining of animation
        do {  
          commandCount += 1;
          readFile(readFileHandle, (INT8U*)&seqHdr, readBufferPtr, sizeof(seq_header_t));
          dnm_ucli_printf("Command Count : %d  FF Type : %d, Stop: %d, Index: %d\r\n", commandCount, seqHdr.type, seqHdr.stop, seqHdr.index);
          //OSTimeDly(3*PERIOD); 
          readBufferPtr += sizeof(seq_header_t);


          switch(seqHdr.type) {
            case SWIPE_UP:
            case SWIPE_DOWN:
            case LINEAR_FADE:
               readFile(readFileHandle, (INT8U*)&scene, readBufferPtr, sizeof(scene_t));
               readBufferPtr += sizeof(scene_t);
               songTime += scene.duration + scene.backPorch;
               break;
               
            case INIT:
               // Set songTime = 1, so backPorch = 1 - this queues up the first transtion to occur after the first wait period
               songTime = 1;
               break;
               
            case END:
               stopSong = 1;  // Reached end before starting
               break;
               
            case SHIFT:
               readFile(readFileHandle, (INT8U*)&scene, readBufferPtr, sizeof(scene_t));
               readBufferPtr += sizeof(scene_t);
               songTime += scene.duration + scene.backPorch;

               readFile(readFileHandle, (INT8U*)&shift, readBufferPtr, sizeof(shift_t));
               readBufferPtr += sizeof(shift_t);
               songTime += shift.frontPorch;              
               break;
               
            default:
               dnm_ucli_printf("WARNING: unexpected song header type %x\r\n", seqHdr.type);
               break;
          } 
        } while (startTime.offset > songTime);
        
        // Set Ext Flash Read Address
        if (seqHdr.type == SHIFT) {
          // If the start time offset lands in the middle of a shift, just hold the ending phase
          flashAddress                  = SHIFT_BASE + (((INT32U) seqHdr.index) << 12) + (INT32U) shift.endPhase + 4;  // Set start address 4 bytes in
        } else {
          flashAddress                  = (((INT32U) seqHdr.index) << 7) + 4;  // Set start address 4 bytes in
        }
        spiTxBuf32[0] = ((flashAddress << 24) & 0xFF000000) |
                        ((flashAddress >> 8 ) & 0x0000FF00) | 
                        ((flashAddress << 8 ) & 0x00FF0000);  // Endianess Swap - note address is only 24 bit
        
        spiTransfer.transactionLen     = 124;
        // Read Scene
        serialFlashReadData(spiTransfer, dnErr); 
        // Set Initial Start LED values

        for (pixel=0;pixel<NUM_PIXELS-1;pixel++) {
          for (comp=0;comp<NUM_COMPS;comp++) {
            startEnd.comp[end][pixel][comp] = (INT8U) spiNetApp_vars.spiRxBuffer[pixel * NUM_COMPS + comp + 4];
          }
        }
        // Load LEDs - this will be redundant for offset = 0 as this will reload the Init scene.
        for (pixel=0;pixel<NUM_PIXELS-1;pixel++) {
          spiTxBuf32[pixel+1] = 0x000000FF + (startEnd.comp[end][pixel][RED] << 24) + (startEnd.comp[end][pixel][GREEN] << 16) + (startEnd.comp[end][pixel][BLUE] << 8);
        }
        spiTxBuf32[0] = 0x00000000;     // Set first 4 bytes in SPI Transfer to sync LEDs
        loadLEDs(spiTransfer, dnErr);  
        
        backPorch = songTime - startTime.offset;
        startBackPorch = 1;
          
        currentIndex = seqHdr.index;  
        
        // Start Animation
        while (stopSong == 0) {  
          if (startBackPorch == 1) {
            // "copy" end scene to start scene
            transitionCount = 0;
            if ((seqHdr.type == SWIPE_DOWN) || (seqHdr.type == SWIPE_UP)) {
              lastSeqSwipe = 1;
            } 
            else {
              lastSeqSwipe = 0;
            }
            // Load new sequence header
            readFile(readFileHandle, (INT8U*)&seqHdr, readBufferPtr, sizeof(seq_header_t));
            if (((seqHdr.type == SWIPE_DOWN) || (seqHdr.type == SWIPE_UP)) && (lastSeqSwipe == 1) && (swipeStart == 0) && (seqHdr.stop > 30))
              // Swipe start = 0 followed by swipe start = 1 keep old end and start arrays
              lastSeqSwipe = 1; // do nothing
            else {
              holdStart       = start;
              start           = end;
              end             = holdStart;
            }
            if ((seqHdr.type == LINEAR_FADE) && (lastSeqSwipe == 1)) {
              for (pixel=0;pixel<NUM_PIXELS-1;pixel++) {
                for (comp=0;comp<NUM_COMPS;comp++) {
                    startEnd.comp[start][pixel][comp] = (INT8U) ((current.comp[pixel][comp] >> 23) & 0x000000FF);
                }
              }
            }
            dnm_ucli_printf("Type : %d, Stop: %d, Index: %d, Time: %d\r\n", seqHdr.type, seqHdr.stop, seqHdr.index, songTime);
            readBufferPtr += sizeof(seq_header_t);
            switch(seqHdr.type) {
              case SWIPE_UP:
              case SWIPE_DOWN:
              case LINEAR_FADE:
                 readFile(readFileHandle, (INT8U*)&scene, readBufferPtr, sizeof(scene_t));
                 readBufferPtr += sizeof(scene_t);
                 break;
               
              case INIT:
                 dnm_ucli_printf("WARNING: unexpected INIT Scene at time %d\r\n", songTime);
                 break;
               
              case END:
                 stopSong = 1;  
                 for (pixel=0;pixel<NUM_PIXELS-1;pixel++) {       
                   spiTxBuf32[pixel+1] = 0x000000FF;
                 }

                 break;
               
              case SHIFT:
                readFile(readFileHandle, (INT8U*)&scene, readBufferPtr, sizeof(scene_t));
                readBufferPtr += sizeof(scene_t);

                readFile(readFileHandle, (INT8U*)&shift, readBufferPtr, sizeof(shift_t));
                readBufferPtr += sizeof(shift_t);          

                break;
               
              default:
                dnm_ucli_printf("WARNING: unexpected song header type %x\r\n", seqHdr.type);
                break;
            }
            // Initialize data for upcoming transition
            if ((seqHdr.type == SWIPE_UP) || (seqHdr.type == SWIPE_DOWN) || (seqHdr.type == LINEAR_FADE) || (seqHdr.type == END)) {
              flashAddress                  = (((INT32U) seqHdr.index) << 7) + 4;  // Set start address 4 bytes in
              spiTxBuf32[0] = ((flashAddress << 24) & 0xFF000000) |
                              ((flashAddress >> 8 ) & 0x0000FF00) | 
                              ((flashAddress << 8 ) & 0x00FF0000);  // Endianess Swap - note SPI address is only 24 bit
              spiTransfer.transactionLen     = 124;
              // Read Scene
              serialFlashReadData(spiTransfer, dnErr); 
              // Set Initial Start LED values
              flickerOnNext = 0;
              for (pixel=0;pixel<NUM_PIXELS-1;pixel++) {
                for (comp=0;comp<NUM_COMPS;comp++) {
                  startEnd.comp[end][pixel][comp] = spiNetApp_vars.spiRxBuffer[pixel * NUM_COMPS + comp + 4];
                }
                if (startEnd.comp[end][pixel][FLICKER] > 0) {
                  flickerOnNext = 1;
                }
              }
              if (seqHdr.type == LINEAR_FADE) {
                for (pixel=0;pixel<NUM_PIXELS-1;pixel++) {
                  for (comp=0;comp<NUM_COMPS;comp++) {
                    current.comp[pixel][comp] = (INT32S) (startEnd.comp[start][pixel][comp] << 23);
                    delta.comp[pixel][comp] = (((INT32S) (startEnd.comp[end][pixel][comp] << 23)) - current.comp[pixel][comp]) / ((INT32S) scene.duration);
                  }
                }
                position = 1;
              } else if (seqHdr.type == SWIPE_UP) {
                if (seqHdr.stop > 30) {
                   swipeStart = 1;
                   position = (0x7F & seqHdr.stop) << 16;
                   positionDelta = ((INT32U) (0x7F & seqHdr.stop) << 16) / ((INT32U) scene.duration);
                } else {
                   swipeStart = 0;
                   position = 0 << 16;
                   positionDelta = ((INT32U) (31 - (0x7F & seqHdr.stop)) << 16) / ((INT32U) scene.duration);
                }
              } else if (seqHdr.type == SWIPE_DOWN) {
                if (seqHdr.stop > 30) {
                   swipeStart = 1;
                   position = (INT32U) (0x7F & seqHdr.stop) << 16;
                   positionDelta = ((INT32U) (31 - (0x7F & seqHdr.stop)) << 16) / ((INT32U) scene.duration);
                } else {
                   swipeStart = 0;
                   positionDelta = ((INT32U) ((31 - (0x7F & seqHdr.stop)) << 16)) / ((INT32U) scene.duration);
                   position = 30 << 16;
                }                  
              }
            } else if (seqHdr.type == SHIFT) { 
              if (shift.endPhase > shift.startPhase) {
                rightShift = 1;
                positionDelta = ((INT32U) ((shift.endPhase - shift.startPhase) << 16) ) / ((INT32U) scene.duration);
              } else {
                rightShift = 0;
                positionDelta = ((INT32U) ((shift.startPhase - shift.endPhase) << 16) ) / ((INT32U) scene.duration);
              }
              position      = ((INT32U) shift.startPhase) << 16;
              flashAddress  = SHIFT_BASE + (((INT32U) seqHdr.index) << 12) + (INT32U) shift.startPhase + 3 + (INT32U) rightShift;  // Set start address 4 bytes in
              spiTxBuf32[0] = ((flashAddress << 24) & 0xFF000000) |
                              ((flashAddress >> 8 ) & 0x0000FF00) | 
                              ((flashAddress << 8 ) & 0x00FF0000);  // Endianess Swap - note address is only 24 bit
              spiTransfer.transactionLen     = 128;
              // Read Scene
              serialFlashReadData(spiTransfer, dnErr); 
              // Shift only uses start 
              flickerOn = 0;
              for (pixel=0;pixel<NUM_PIXELS;pixel++) {
                for (comp=0;comp<NUM_COMPS;comp++) {
                  startEnd.comp[start][pixel][comp] = spiNetApp_vars.spiRxBuffer[pixel * NUM_COMPS + comp + 4];  // skip first 4 empty values
                }
                if (startEnd.comp[start][pixel][FLICKER] > 0) {
                  flickerOn = 1;
                }
              }
            }
           
            startBackPorch = 0;
          } //(startBackPorch == 1)
          
          /// ****** BACK PORCH **** ///
          
          if (backPorch > 0) {
            backPorch -= 1;
            flickerSpeed = 25;
            flickerDiv += 1;                            

            if (flickerDiv >= flickerSpeed) {
              flickerDiv = 0;
            }
            if ((flickerOn == 1) && (flickerDiv == 1)) {
              for (pixel=0;pixel<NUM_PIXELS-1;pixel++) {
                for (comp=1;comp<NUM_COMPS;comp++) {  // Don't include flicker comp in calcs
                  if (current.comp[pixel][FLICKER] > 0) {
                     pixFlickerPhase = (INT16U) pixel * 17 + flickerPhase;
                     flicker.comp[pixel][comp] = (flickerCurr.comp[pixel][comp] >> 16) * ((1 << 16) - Rand((INT8U) pixFlickerPhase) * (flickerCurr.comp[pixel][FLICKER]>>23));
                  } else {
                     flicker.comp[pixel][comp] = flickerCurr.comp[pixel][comp];
                  }
                }
              spiTxBuf32[pixel+1] = 0x000000FF | (((INT32U) (flicker.comp[pixel][RED])   <<  1) & 0xFF000000 | 
                                                  ((INT32U) (flicker.comp[pixel][GREEN]) >>  7) & 0x00FF0000 | 
                                                  ((INT32U) (flicker.comp[pixel][BLUE])  >> 15) & 0x0000FF00);
              } 
            }
 
          } else {
            // Calculate next pattern
            switch(seqHdr.type) {
              case SWIPE_UP:
                oldWholePosition = (INT16U) (position >> 16);
                if (swipeStart == 0) {
                  position += positionDelta;
                } else if (position >= positionDelta) {
                  position -= positionDelta;
                } else {
                  position = 0;
                }
                wholePosition = (INT16U) (position >> 16);
                fractionalPosition = position - ((INT32U) wholePosition << 16);
                remainingPosition = (1 << 16) - fractionalPosition;
                for (pixel=0;pixel<NUM_PIXELS-1;pixel++) {
                  for (comp=0;comp<NUM_COMPS;comp++) {
                    if (pixel<(wholePosition)) {
                      current.comp[pixel][comp] = (INT32S) (startEnd.comp[end][pixel][comp] << 23);
                    } else if (pixel == wholePosition) {
                      current.comp[wholePosition][comp] = (INT32S) (((startEnd.comp[end][wholePosition][comp]  * fractionalPosition) << 7) +
                                                                    ((startEnd.comp[start][wholePosition][comp] * remainingPosition) << 7));
                    } else {
                      current.comp[pixel][comp] = (INT32S) (startEnd.comp[start][pixel][comp] << 23);
                    }
                  }
                  spiTxBuf32[pixel+1] = 0x000000FF | (((INT32U) (current.comp[pixel][RED])   <<  1) & 0xFF000000 | 
                                                      ((INT32U) (current.comp[pixel][GREEN]) >>  7) & 0x00FF0000 | 
                                                      ((INT32U) (current.comp[pixel][BLUE])  >> 15) & 0x0000FF00);
                }
                break;
            case SWIPE_DOWN:
                oldWholePosition = (INT16U) (position >> 16);
                if (swipeStart == 1) {
                  position += positionDelta;
                } else if (position >= positionDelta) {
                  position -= positionDelta;
                } else {
                  position = 0;
                }
                wholePosition = (INT16U) (position >> 16);
                remainingPosition = position - ((INT32U) wholePosition << 16);
                fractionalPosition = (1 << 16) - remainingPosition;
                for (pixel=0;pixel<NUM_PIXELS-1;pixel++) {
                  for (comp=0;comp<NUM_COMPS;comp++) {
                    if ((pixel<32) && (pixel>wholePosition)) {
                      current.comp[pixel][comp] = (INT32S) (startEnd.comp[end][pixel][comp] << 23);
                    } else if (pixel == wholePosition) {
                      current.comp[wholePosition][comp] = (INT32S) (((startEnd.comp[end][wholePosition][comp]  * fractionalPosition) << 7) +
                                                                    ((startEnd.comp[start][wholePosition][comp] * remainingPosition) << 7));
                    } else {
                      current.comp[pixel][comp] = (INT32S) (startEnd.comp[start][pixel][comp] << 23);
                    }
                  }
                  spiTxBuf32[pixel+1] = 0x000000FF | (((INT32U) (current.comp[pixel][RED])   <<  1) & 0xFF000000 | 
                                                      ((INT32U) (current.comp[pixel][GREEN]) >>  7) & 0x00FF0000 | 
                                                      ((INT32U) (current.comp[pixel][BLUE])  >> 15) & 0x0000FF00);
                }
                
                break;
              case LINEAR_FADE:
                for (pixel=0;pixel<NUM_PIXELS-1;pixel++) {
                  for (comp=0;comp<NUM_COMPS;comp++) {
                    current.comp[pixel][comp] += delta.comp[pixel][comp];
                  }
                spiTxBuf32[pixel+1] = 0x000000FF | (((INT32U) (current.comp[pixel][RED])   <<  1) & 0xFF000000 | 
                                                    ((INT32U) (current.comp[pixel][GREEN]) >>  7) & 0x00FF0000 | 
                                                    ((INT32U) (current.comp[pixel][BLUE])  >> 15) & 0x0000FF00);
                }     

              break;
                 
              case INIT:
                // Do Nothing
                break;
               
              case END:
                stopSong = 1;  // Turn off all LEDs
                dnm_ucli_printf("*** Stopping Song ***\r\n");
                for (pixel=0;pixel<NUM_PIXELS-1;pixel++) {       
                  spiTxBuf32[pixel+1] = 0x000000FF;
                }

                break;
               
              case SHIFT:
                oldWholePosition = (INT16U) (position >> 16);
                if (rightShift == 1) {
                   position += positionDelta;
                } else {
                   position -= positionDelta;
                }
                wholePosition = (INT16U) (position >> 16);
                if (rightShift == 1) {
                  fractionalPosition = position - (((INT32U) wholePosition) << 16);
                  remainingPosition = (1 << 16) - fractionalPosition;
                } else {
                  fractionalPosition = position - (((INT32U) wholePosition) << 16);
                  remainingPosition = (1 << 16) - fractionalPosition;
                }
                if (wholePosition != oldWholePosition) {
                  flashAddress  = SHIFT_BASE + (((INT32U) seqHdr.index) << 12) + (INT32U) wholePosition + 3 + (INT32U) rightShift;  // Set start address 4 bytes in
                  spiTxBuf32[0] = ((flashAddress << 24) & 0xFF000000) |
                                  ((flashAddress >> 8 ) & 0x0000FF00) | 
                                  ((flashAddress << 8 ) & 0x00FF0000);  // Endianess Swap - note address is only 24 bit
                  spiTransfer.transactionLen     = 128;
                  // Read Scene
                  serialFlashReadData(spiTransfer, dnErr); 
                  // Shift only uses start 
                  flickerOn = 0;
                  for (pixel=0;pixel<NUM_PIXELS;pixel++) {
                    for (comp=0;comp<NUM_COMPS;comp++) {
                      startEnd.comp[start][pixel][comp] = spiNetApp_vars.spiRxBuffer[pixel * NUM_COMPS + comp + 4];  // skip first 4 empty values
                    }
                    if (startEnd.comp[start][pixel][FLICKER] > 0) {
                      flickerOn = 1;
                    }
                  }

                }
                for (pixel=0;pixel<NUM_PIXELS-1;pixel++) {
                  for (comp=0;comp<NUM_COMPS;comp++) {
                    current.comp[pixel][comp] = (INT32S) (((startEnd.comp[start][pixel][comp]   * fractionalPosition) << 7) +
                                                          ((startEnd.comp[start][pixel+1][comp] * remainingPosition) << 7));
                  }
                  spiTxBuf32[pixel+1] = 0x000000FF | (((INT32U) (current.comp[pixel][RED])   <<  1) & 0xFF000000 | 
                                                      ((INT32U) (current.comp[pixel][GREEN]) >>  7) & 0x00FF0000 | 
                                                      ((INT32U) (current.comp[pixel][BLUE])  >> 15) & 0x0000FF00);
                }
                
                break;
               
               default:
                 dnm_ucli_printf("WARNING: unexpected song header type %x\r\n", seqHdr.type);
                 break;
             } 
             transitionCount += 1;
           } // else "(backPorch = 0)" 
          
           spiTransfer.slaveSelect = DN_SPIM_SS_0n;           
           // get the current time
           dn_getNetworkTime(
             &currentASN,
             &currentUTC
           );
           // Convert UTC Time to time in ms
           UTC64 = (((INT64U) currentUTC.sec) * 1000) + (((INT64U) currentUTC.usec + 500) / 1000);
         
           if (nextLEDLoadTime > UTC64) {
             // figure out how long to wait
             timeToWaitMs = nextLEDLoadTime - UTC64;
             // start the timer
             synctemp_v.sampleTaskStackTimer->OSTmrDly = timeToWaitMs;
             OSTmrStart(synctemp_v.sampleTaskStackTimer, &osErr);
             ASSERT (osErr == OS_ERR_NONE);
      
             // wait for timer to expire
             OSSemPend(
               synctemp_v.sampleTaskStackTimerSem,     // pevent
               0,                                      // timeout
               &osErr                                  // perr
             );
             ASSERT (osErr == OS_ERR_NONE);
           } else {
             numSkips += 1;
           }
           
           if ((backPorch == 0) || (flickerOn == 1) || (flickerOn == 0)) {
             spiTxBuf32[0] = 0x00000000;
             loadLEDs(spiTransfer, dnErr);

           } 
           if (minWait > (INT32U) timeToWaitMs) {
             minWait = timeToWaitMs;
           }
           nextLEDLoadTime += PERIOD;
           ++songTime; 
           ++flickerPhase;
           if (transitionCount >= scene.duration) {
             startBackPorch = 1;
             flickerOn = flickerOnNext;
             backPorch = scene.backPorch;  
             for (pixel=0;pixel<NUM_PIXELS-1;pixel++) {
               for (comp=0;comp<NUM_COMPS;comp++) {
                 flickerCurr.comp[pixel][comp] = current.comp[pixel][comp];
               }
             }  
             flickerDiv = 0;
             
           }         
         }  // while (stopSong == 0)
       }  // while ((readFileInfo.len - readBufferPtr) > 0)
     }  // while (stopSong == 0)
     dnm_ucli_printf("Song %d done.  Min Wait = %d, # of skips = %d\r\n", song, minWait, numSkips);
     songPlaying   = 0;
   }  // while (1) -  this is a task, it executes forever
} 

void sampleTaskStackTimer_cb(void* pTimer, void *pArgs) {
   INT8U  osErr;
   
   // post the semaphore
   osErr = OSSemPost(synctemp_v.sampleTaskStackTimerSem);
   ASSERT(osErr == OS_ERR_NONE);
}

static void processRxTask(void* unused) {
   INT8U                     osErr;
   app_payload_ht*           appHdr;
   INT8U                     command;
   INT8U                     dnErr;
   // USES SPI pkBuf size as it is larger - not used in spi_net_app.c
   loc_sendtoNW_t*           pkToSend;
   led_payload_ht*           payloadToSend;
   INT8U                     rc;
   INT8U                     payload[90];
   INT32U                    i, j;
   INT8U                     pkBuf[sizeof(loc_sendtoNW_t) + APP_DATA_BUF_SIZE];
   INT8U                     flashState;
   INT8U                     writeLen;
   INT8U                     payloadSize;
   INT8U                     songPayloadSize;
   INT8U                     fragment;
   INT8U                     commandCount;
   INT8U                     song1data;
   dn_fs_handle_t            eraseFileHandle, writeFileHandle, readFileHandle;
   dn_fs_fileinfo_t          readFileInfo;
   time_t*                   startTimePtr;  
   INT32U                    nowS;
   INT32U                    nowuS;
   INT32U                    readBufferPtr;
   INT16U                    readFragment;
   INT8U                     lastFragment;
   INT8U                     backoffCount;
   dn_api_rsp_get_moteinfo_t *myMacAddr;
   INT8U                     reply[sizeof(dn_api_rsp_get_moteinfo_t)];
   INT8U                     respLen;
   INT32U                    color[5];
   INT16U                    deviceID;
   INT32U                    moteNumPattern;
   INT8U                     moteNum;
   
      //===== initialize SPI
   // open the SPI device
   // see doxygen documentation on maxTransactionLenForCPHA_1 when setting
   spiOpenArgs.maxTransactionLenForCPHA_1 = 0;
   dnErr = dn_open(
      DN_SPI_DEV_ID,
      &spiOpenArgs,
      sizeof(spiOpenArgs)
   );
   ASSERT((dnErr == DN_ERR_NONE) || (dnErr == DN_ERR_STATE));
   
   dnErr = dnm_loc_getParameterCmd(
                                   DN_API_PARAM_MOTEINFO,
                                   reply,
                                   0,
                                   &respLen,
                                   &rc 
                                 );	
   myMacAddr = (dn_api_rsp_get_moteinfo_t*) reply;
   
  
   // initialize spi communication parameters
   spiTransfer.txData             = spiNetApp_vars.spiTxBuffer;
   spiTransfer.rxData             = spiNetApp_vars.spiRxBuffer;
   spiTransfer.transactionLen     = sizeof(spiNetApp_vars.spiTxBuffer);
   spiTransfer.numSamples         = 1;
   spiTransfer.startDelay         = 0;
   spiTransfer.clockPolarity      = DN_SPI_CPOL_0;
   spiTransfer.clockPhase         = DN_SPI_CPHA_0;
   spiTransfer.bitOrder           = DN_SPI_MSB_FIRST;
   spiTransfer.slaveSelect        = DN_SPIM_SS_0n;
   spiTransfer.clockDivider       = DN_SPI_CLKDIV_2;
   spiTransfer.rxBufferLen        = sizeof(spiNetApp_vars.spiRxBuffer);
   spiTxBuf32                     = (INT32U *)&spiNetApp_vars.spiTxBuffer[0];
   
   
   // Self Test for flash connection - blink white/black/white...  to indicate failure, else do nothing
   deviceID = serialFlashReadDevID(spiTransfer, dnErr);
   if (deviceID != 0x0116) {
     spiTxBuf32[0] = 0x00000000;
     for (i=0; i<5; i++) {
       for (j=0;j<NUM_PIXELS-1;j++) {
         spiTxBuf32[j+1] = 0xFFFFFFFF;
       }
       loadLEDs(spiTransfer, dnErr);
       OSTimeDly(20*PERIOD);  
       for (j=0;j<NUM_PIXELS-1;j++) {
         spiTxBuf32[j+1] = 0x000000FF;
       }
       loadLEDs(spiTransfer, dnErr);
       OSTimeDly(20*PERIOD);  
     }
   }

   // Look up tube number and corresponding bit pattern
   switch(myMacAddr->serialNumber[7]) {
     case 0x6E:
       if (myMacAddr->serialNumber[6] == 0xB2) {
         moteNum = 1;
         moteNumPattern = 0x00000001;
       } else {
         moteNum = 5;  // 59-61-6E
         moteNumPattern = 0x0000001F;
       }
         
       break;     
     case 0xEE:
       moteNum = 2;
       moteNumPattern = 0x00000005;
         
       break;
     case 0x14:
       moteNum = 3;
       moteNumPattern = 0x00000015;
         
       break;
     case 0x0F:
       moteNum = 4;
       moteNumPattern = 0x00000055;
         
       break;
     case 0x13:
       moteNum = 6;
       moteNumPattern = 0x0000009F;
         
       break;
     case 0x62:
       moteNum = 7;
       moteNumPattern = 0x0000029F;
         
       break;
     case 0x27:
       moteNum = 8;
       moteNumPattern = 0x00000A9F;
         
       break;
     case 0xD3:
       moteNum = 9;
       moteNumPattern = 0x00002A9F;
         
       break;
     case 0xB3:
       moteNum = 10;
       moteNumPattern = 0x00000F9F;
         
       break;
     case 0x75:
       moteNum = 11;
       moteNumPattern = 0x0004F9F;
         
       break;
     case 0xE0:
       moteNum = 12;
       moteNumPattern = 0x0014F9F;
         
       break;
     case 0xB2:
       moteNum = 13;
       moteNumPattern = 0x0094F9F;
         
       break;
     case 0x1D:
       moteNum = 14;
       moteNumPattern = 0x0294F9F;
         
       break;
     default:
       moteNum = 0;
       moteNumPattern = 0xFFFF0000;
       dnm_ucli_printf("Could not find MAC Address : %02x:%02x:%02x:%02x:%02x:%02x:%02x:%02x\r\n", myMacAddr->serialNumber[0], myMacAddr->serialNumber[1], myMacAddr->serialNumber[2], myMacAddr->serialNumber[3], myMacAddr->serialNumber[4], myMacAddr->serialNumber[5], myMacAddr->serialNumber[6], myMacAddr->serialNumber[7]);

   }
   
   // Display Bit Pattern
   for (j=0;j<NUM_PIXELS-1;j++) {
     if (((moteNumPattern >> j) & 0x00000001) == 1) {
       spiTxBuf32[j+1] = 0xFFFFFFFF;
     } else {
       spiTxBuf32[j+1] = 0x000000FF;
     }
   }
   spiTxBuf32[0] = 0x00000000;
   loadLEDs(spiTransfer, dnErr);
   OSTimeDly(150*PERIOD);  
   // Turn to black
   for (j=1;j<NUM_PIXELS;j++) {
     spiTxBuf32[j] = 0x000000FF;
   }
   loadLEDs(spiTransfer, dnErr);
     
   OSTimeDly(350*PERIOD);  
   // wait for mote to join
   OSSemPend(fakeJoin, 0, &osErr);
   ASSERT(osErr==OS_ERR_NONE);
   lockData();
   synctemp_v.isJoined = 0x01;
   unlockData();

         
   // fill in packet metadata
   pkToSend = (loc_sendtoNW_t*)pkBuf;
   pkToSend->locSendTo.socketId          = loc_getSocketId();
   pkToSend->locSendTo.destAddr          = DN_MGR_IPV6_MULTICAST_ADDR;
   pkToSend->locSendTo.destPort          = SYNCTEMP_UDP_PORT;
   pkToSend->locSendTo.serviceType       = DN_API_SERVICE_TYPE_BW;   
   pkToSend->locSendTo.priority          = DN_API_PRIORITY_MED;   
   pkToSend->locSendTo.packetId          = 0xFFFF;
   
   payloadToSend = (led_payload_ht*)pkToSend->locSendTo.payload;
   
   flashState    = FLASH_WRITTEN;
   commandCount  = 0;
   command       = 0;

   
   while (1) { // this is a task, it executes forever
      
      // wait for the rx packet to be ready
      OSSemPend(synctemp_v.rxPkReady, 0, &osErr);
      ASSERT(osErr==OS_ERR_NONE);
      
      // print received packet
      
      dnm_ucli_printf("rx packet\r\n");
      dnm_ucli_printf("- from:     ");
      printf_buffer(synctemp_v.rxPkSrc.byte,sizeof(dn_ipv6_addr_t));
      dnm_ucli_printf("\r\n");
      dnm_ucli_printf("- payload:  ");
      printf_buffer(synctemp_v.rxPkPayload,synctemp_v.rxPkPayloadLen);
      dnm_ucli_printf(" (%d bytes)\r\n", synctemp_v.rxPkPayloadLen);
      

            // trick to be able to use "break"
      do {
         
         // parse header
         command      = synctemp_v.rxPkPayload[0];  
         if (command == PKT_COM_COUNT_RESET) {
           commandCount = 0;
         }
         if (commandCount == synctemp_v.rxPkPayload[1]) {
            dnm_ucli_printf("Duplicate Command = %x, Count = %d\r\n", command, commandCount);
         } else {
            commandCount = synctemp_v.rxPkPayload[1];
            dnm_ucli_printf("Command = %x, Count = %d\r\n", command, commandCount);
         switch(command) {
            case PKT_SET_START_TIME:
               // Recieved Start of song notification:
               if (songPlaying != 1) {
                 song             = synctemp_v.rxPkPayload[2];
                 startTimePtr     = (time_t*) &synctemp_v.rxPkPayload[3];
                 startTime.S      = startTimePtr->S;
                 startTime.uS     = startTimePtr->uS;
                 startTime.offset = startTimePtr->offset;
                 dnm_ucli_printf("\r\nSong[%d] Start Time: = %u S, %u uS, Offset: %d\r\n\r\n", song, startTime.S, startTime.uS, startTime.offset);
                 OSSemPost(startSong);
                 // get current network time
                 dn_getNetworkTime(
                    &currentASN,
                    &currentUTC
                 );
                 nowS  = (INT32U)currentUTC.sec;
                 nowuS = (INT32U)currentUTC.usec;

                 dnm_ucli_printf("\r\n***  Current Time = %u S, %u uS\r\n\r\n", nowS, nowuS);

                 // send ACK
                 payloadSize                    = 1;
                 payloadToSend->cmdId           = command;
                 payload[0]                     = 0x01;
                 memcpy(payloadToSend->payload,payload,payloadSize);
      
                 dnErr = dnm_loc_sendtoCmd(
                    pkToSend,
                    sizeof(led_payload_ht)+payloadSize,
                    &rc
                 );
                 ASSERT (dnErr == DN_ERR_NONE);
                 if (rc!=DN_ERR_NONE){
                    dnm_ucli_printf("ERROR sending data (RC=%d)\r\n", rc);
                 }         
               }
               
               break;
            case PKT_COM_COUNT_RESET:
               // just send ack
               payloadSize                    = 1;
               payloadToSend->cmdId           = command;
               payload[0]                     = LED_ACK;
               memcpy(payloadToSend->payload,payload,payloadSize);
             
               // send packet
               dnErr = dnm_loc_sendtoCmd(
                  pkToSend,
                  sizeof(led_payload_ht)+payloadSize,
                  &rc
               );
               ASSERT (dnErr == DN_ERR_NONE);
               if (rc!=DN_ERR_NONE){
                  dnm_ucli_printf("ERROR sending PKT COM Count Reset Ack (RC=%d)\r\n", rc);
               }

               break;
            case PKT_STOP:
               // send ack / stop song
               payloadSize                    = 1;
               payloadToSend->cmdId           = command;
               payload[0]                     = LED_ACK;
               memcpy(payloadToSend->payload,payload,payloadSize);
             
               // send packet
               dnErr = dnm_loc_sendtoCmd(
                  pkToSend,
                  sizeof(led_payload_ht)+payloadSize,
                  &rc
               );
               ASSERT (dnErr == DN_ERR_NONE);
               if (rc!=DN_ERR_NONE){
                  dnm_ucli_printf("ERROR sending Stop Song Ack (RC=%d)\r\n", rc);
               }
               stopSong = 1;

               break;
            case PKT_EXTERNAL_FLASH_ERASE:
               // filter length
               if (flashState != FLASH_ERASED) {
                  serialFlashWriteEnable(spiTransfer, dnErr);
                  i = 0;
                  serialFlashErase(i, spiTransfer, dnErr);
                  flashState = FLASH_ERASED;
               }
               payloadSize                    = 1;
               payloadToSend->cmdId           = command;
               payload[0]                     = 0x01;
               memcpy(payloadToSend->payload,payload,payloadSize);
             
               // send packet
               dnErr = dnm_loc_sendtoCmd(
                  pkToSend,
                  sizeof(led_payload_ht)+payloadSize,
                  &rc
               );
               ASSERT (dnErr == DN_ERR_NONE);
               if (rc!=DN_ERR_NONE){
                  dnm_ucli_printf("ERROR sending data (RC=%d)\r\n", rc);
               }

               break;
            case PKT_EXTERNAL_FLASH_WRITE:
               // External Flash SPI Interface:
               // 8-bit command, 24-bit address, byte wide data, with no idle shift clocks
               flashState = FLASH_WRITTEN;
               dnm_ucli_printf("Writing %d bytes to flash address: %0x%0x%0x\r\n", synctemp_v.rxPkPayload[6], synctemp_v.rxPkPayload[4], synctemp_v.rxPkPayload[3], synctemp_v.rxPkPayload[2]);
               serialFlashWriteEnable(spiTransfer, dnErr);
               spiNetApp_vars.spiTxBuffer[0]  = PAGE_PROGRAM;
               spiNetApp_vars.spiTxBuffer[1]  = synctemp_v.rxPkPayload[4];  //skip byte 5, as flash is only 24-bit address and rx packet has 4 address bytes
               spiNetApp_vars.spiTxBuffer[2]  = synctemp_v.rxPkPayload[3];
               spiNetApp_vars.spiTxBuffer[3]  = synctemp_v.rxPkPayload[2];
               writeLen                       = synctemp_v.rxPkPayload[6];
               // loop to copy data
               for (i=0;i<writeLen;i++) {
                  spiNetApp_vars.spiTxBuffer[i+4]  = synctemp_v.rxPkPayload[i+7]; 
               }
               spiTransfer.transactionLen     = writeLen + 4;
               serialFlashProgram(spiTransfer, dnErr);
               // send ACK
               payloadSize                    = 1;
               payloadToSend->cmdId           = command;
               payload[0]                     = 0x01;
               memcpy(payloadToSend->payload,payload,payloadSize);
      
               dnErr = dnm_loc_sendtoCmd(
                  pkToSend,
                  sizeof(led_payload_ht)+payloadSize,
                  &rc
               );
               ASSERT (dnErr == DN_ERR_NONE);
               if (rc!=DN_ERR_NONE){
                  dnm_ucli_printf("ERROR sending data (RC=%d)\r\n", rc);
               }         
               
               break;
            case PKT_SEND_SCENE:
               // External Flash SPI Interface:
               // 8-bit command, 24-bit address, byte wide data, with no idle shift clocks
               dnm_ucli_printf("Reading 120 bytes from flash address: %0x%0x%0x\r\n", synctemp_v.rxPkPayload[4], synctemp_v.rxPkPayload[3], synctemp_v.rxPkPayload[2]);
               spiNetApp_vars.spiTxBuffer[1]  = synctemp_v.rxPkPayload[4];  //skip byte 5, as flash is only 24-bit address and rx packet has 4 address bytes
               spiNetApp_vars.spiTxBuffer[2]  = synctemp_v.rxPkPayload[3];
               spiNetApp_vars.spiTxBuffer[3]  = synctemp_v.rxPkPayload[2];
               spiTransfer.transactionLen     = 124;
               serialFlashReadData(spiTransfer, dnErr);
               // send with read data
               payloadSize                    = 62;
               payloadToSend->cmdId           = command;
               payload[0]                     = 0x01;
               for (fragment=0;fragment<2;fragment++) {
                  payload[1] = fragment + 1;
                  for (j=0;j<60;j++) {
                     payload[j+2] = spiNetApp_vars.spiRxBuffer[fragment*60+j+4];
                  }
                  memcpy(payloadToSend->payload,payload,payloadSize);
      
                  dnErr = dnm_loc_sendtoCmd(
                     pkToSend,
                     sizeof(led_payload_ht)+payloadSize,
                     &rc
                  );
                  ASSERT (dnErr == DN_ERR_NONE);
                  if (rc!=DN_ERR_NONE){
                     dnm_ucli_printf("ERROR sending data (RC=%d)\r\n", rc);
                  }            
               } // for fragment

               break;
               
            case PKT_SONG_ERASE:
               // Erase Song in FileSystem:               
               song = (INT8U) synctemp_v.rxPkPayload[2];
               if (song < 13) {
                  dnErr = cli_listFiles();
                  dnm_ucli_printf("Erasing Song: %s\r\n", songLookup[song]);
                  eraseFileHandle = openFile((char *)songLookup[song]);
                  eraseFile((char *)songLookup[song]);
                  payload[0] = LED_ACK;
                  dnErr = cli_listFiles();
               } else {
                  payload[0] = LED_NAK;
               }

               // send ACK / NAK
               payloadSize                    = 1;
               payloadToSend->cmdId           = command;
               memcpy(payloadToSend->payload,payload,payloadSize);
      
               dnErr = dnm_loc_sendtoCmd(
                  pkToSend,
                  sizeof(led_payload_ht)+payloadSize,
                  &rc
               );
               ASSERT (dnErr == DN_ERR_NONE);
               if (rc!=DN_ERR_NONE){
                  dnm_ucli_printf("ERROR sending data (RC=%d)\r\n", rc);
               }         
               
               break;
               
            case PKT_SONG_APPEND:
               // Append Data to Song in File System:
               song        = (INT8U) synctemp_v.rxPkPayload[2];  
               payloadSize = (INT8U) synctemp_v.rxPkPayload[3];
               for (i=0;i<payloadSize;i++) {
                  payload[i]  = synctemp_v.rxPkPayload[i+4]; 
               }
               writeFileHandle = openFile((char *)songLookup[song]);
               appendFile(writeFileHandle, payload, payloadSize);
               
               // send ACK
               payloadSize                    = 1;
               payloadToSend->cmdId           = command;
               payload[0]                     = LED_ACK;
               memcpy(payloadToSend->payload,payload,payloadSize);
      
               dnErr = dnm_loc_sendtoCmd(
                  pkToSend,
                  sizeof(led_payload_ht)+payloadSize,
                  &rc
               );
               ASSERT (dnErr == DN_ERR_NONE);
               if (rc!=DN_ERR_NONE){
                  dnm_ucli_printf("ERROR sending data (RC=%d)\r\n", rc);
               }         
               
               break;
               
            case PKT_SEND_SONG:
               // Send Entire Song:
               dnm_ucli_printf("Reading song %s", songLookup[song]);
               readBufferPtr  = 0;
               readFragment   = 0;
               lastFragment   = 0x00;
               song           = (INT8U) synctemp_v.rxPkPayload[2];  
               readFileHandle = openFile((char *)songLookup[song]);
               dnErr = dn_fs_getFileInfo(
                  readFileHandle,
                  &readFileInfo
               );
               ASSERT(dnErr >= 0);
               while ((readFileInfo.len - readBufferPtr) > 0) {
                 if ((readFileInfo.len - readBufferPtr) < 81) {
                    songPayloadSize = (INT8U) (readFileInfo.len - readBufferPtr);
                    lastFragment   = 0x01;
                 } else if (readBufferPtr == 0) {
                    if (readFileInfo.len == 84) {
                      lastFragment   = 0x01;
                    }
                    songPayloadSize = 84;  // For first packet include 4 byte init & 10 scenes to avoid splitting a scene across all subsequent packets
                 } else {
                    songPayloadSize = 80;
                 }
                 readFile(readFileHandle, payload, readBufferPtr, (INT32U) songPayloadSize);
                 for (i=0; i<(INT8U) songPayloadSize;i++) {
                    payload[songPayloadSize+3-i] = payload[songPayloadSize-1-i];
                 }
                 payloadToSend->cmdId     = command;
                 payload[0]               = LED_ACK;
                 payload[1]               = (INT8U) (readFragment >> 8);
                 payload[2]               = (INT8U) readFragment;             
                 payload[3]               = lastFragment;
                 memcpy(payloadToSend->payload, payload, songPayloadSize+4);
                 
                 backoffCount = 0;
                 do {
                   dnm_ucli_printf("Sending %d bytes in fragment %d\r\n", songPayloadSize, readFragment);
                   dnErr = dnm_loc_sendtoCmd(
                     pkToSend,
                     sizeof(led_payload_ht)+songPayloadSize+4,
                     &rc
                   );
                   ASSERT (dnErr == DN_ERR_NONE);
                   if (rc == DN_ERR_NONE){
                      break;
                   } else {
                      backoffCount += 1;
                      dnm_ucli_printf("ERROR sending data (RC=%d)\r\n", rc);
                      OSTimeDly(250*backoffCount);
                   }         
                 } while (rc != DN_ERR_NONE);
                 readBufferPtr += songPayloadSize;
                 readFragment      += 1;
               }


               break;

            default:
               dnm_ucli_printf("WARNING: unexpected cmdId %d\r\n", appHdr->cmdId);
               break;
         }
         }
      } while(0);
      // unlock the rx packet
      unlockRxPk();
   }
}

//=========================== helpers =========================================


//===== network

/**
\brief Callback function when receiving a packet OTA.

\param[in] rxFrame The received packet.
\para[in] length  The length of the notification, including the metadata
   (#dn_api_loc_notif_received_t).

\return DN_ERR_NONE always
*/
dn_error_t rxNotif(dn_api_loc_notif_received_t* rxFrame, INT8U length) {
   INT8U                          payloadLen;

   // calc data size
   payloadLen = length-sizeof(dn_api_loc_notif_received_t);
   
   // filter packet
   if (rxFrame->socketId!=loc_getSocketId()) {
      // wrong destination UDP port
      return DN_ERR_NONE;
   }
   if (htons(rxFrame->sourcePort)!=SYNCTEMP_UDP_PORT) {
      // wrong source UDP port
      return DN_ERR_NONE;
   }
   if (payloadLen>MAX_RX_PAYLOAD) {
      // payload too long
      return DN_ERR_NONE;
   }
   
   // if you get here, the packet will be passed to sampleTask
   
   // lock the rx packet information
   // NOTE: will be unlocked by sampleTask when ready
   lockRxPk();
   
   // copy packet information to module variables
   memcpy(synctemp_v.rxPkSrc.byte,rxFrame->sourceAddr.byte,DN_IPV6_ADDR_SIZE);
   memcpy(synctemp_v.rxPkPayload,rxFrame->data,payloadLen);
   synctemp_v.rxPkPayloadLen = payloadLen;
   
   // tell sampleTask the rx packet is ready
   OSSemPost(synctemp_v.rxPkReady);
   
   // NOTE: sampleTask will call unlockRxPk()
   
   return DN_ERR_NONE;
}

//===== formatting

void printf_buffer(INT8U* buf, INT8U len) {
   INT8U i;
   
   for (i=0;i<len;i++) {
      dnm_ucli_printf("%02x ",buf[i]);
   }
}

// configuration
void setPeriod(INT32U newPeriod) {
   INT8U      osErr;
   BOOLEAN    rc;
   INT32U     currentPeriod;
   
   // get current period
   lockData();
   currentPeriod = synctemp_v.app_cfg.reportPeriod;
   unlockData();
   
   // abort if nothing to change
   if (currentPeriod==newPeriod) {
      return;
   }
   
   // update period
   lockData();
   synctemp_v.app_cfg.reportPeriod = newPeriod;
   unlockData();
   
   // write to file
   syncToConfigFile();
   
   // print period
   dnm_ucli_printf(
      "Configuration updated: reportPeriod = %d seconds\r\n",
      newPeriod
   );
   
   // rearm timer
   rc = OSTmrStop(
      synctemp_v.sampleTaskStackTimer, // ptmr
      OS_TMR_OPT_NONE,                 // opt
      NULL,                            // callback_arg
      &osErr                           // perr
   );
   ASSERT(rc==OS_TRUE);
   ASSERT(osErr == OS_ERR_NONE);
   
   // call the timer callback
   sampleTaskStackTimer_cb(NULL,NULL);
   
}

//===== configuration file

void loadConfigFile(){
   dn_error_t        dnErr;
   dn_fs_handle_t    configFileHandle;
   
   configFileHandle = dn_fs_find(APP_CONFIG_FILENAME);
   
   if (configFileHandle>=0) {
      // file found: read it
      
      // open file
      configFileHandle = dn_fs_open(
         APP_CONFIG_FILENAME,
         DN_FS_OPT_CREATE,
         sizeof(app_cfg_t),
         DN_FS_MODE_OTH_RW
      );
      ASSERT(configFileHandle >= 0);
      
      // read file
      lockData();
      dnErr = dn_fs_read(
         configFileHandle,
         0, // offset
         (INT8U*)&(synctemp_v.app_cfg),
         sizeof(app_cfg_t)
      );
      unlockData();
      ASSERT(dnErr>=0);
      
      // close file
      dn_fs_close(configFileHandle);
      
      dnm_ucli_printf(
         "Current configuration: reportPeriod = %u seconds\r\n",
         synctemp_v.app_cfg.reportPeriod
      );
      
   } else {
      // file not found: create it
      
      // prepare file content
      lockData();
      synctemp_v.app_cfg.reportPeriod = DEFAULT_RPT_PERIOD;
      unlockData();
      
      // create file
      dnm_ucli_printf("Create config file\r\n");
      configFileHandle = dn_fs_open(
         APP_CONFIG_FILENAME,
         DN_FS_OPT_CREATE,
         sizeof(app_cfg_t),
         DN_FS_MODE_SHADOW
      );
      ASSERT(configFileHandle>=0);
      
      // write file
      lockData();
      dnErr = dn_fs_write(
         configFileHandle,
         0, // offset
         (INT8U*)&(synctemp_v.app_cfg),
         sizeof(app_cfg_t)
      );
      unlockData();
      ASSERT(dnErr >= 0);
      
      // close file
      dn_fs_close(configFileHandle);
      
      dnm_ucli_printf(
         "Default Config created:  reportPeriod = %u seconds\r\n",
         synctemp_v.app_cfg.reportPeriod
      );
   }
}

void syncToConfigFile() {
   dn_error_t          dnErr;
   dn_fs_handle_t      configFileHandle;
   
   // open file
   configFileHandle = dn_fs_open(
      APP_CONFIG_FILENAME,
      DN_FS_OPT_CREATE,
      sizeof(app_cfg_t),
      DN_FS_MODE_OTH_RW
   );
   ASSERT(configFileHandle >= 0);
   
   // write file
   lockData();
   dnErr = dn_fs_write(
      configFileHandle,
      0, // offset
      (INT8U*)&(synctemp_v.app_cfg),
      sizeof(app_cfg_t)
   );
   unlockData();
   ASSERT(dnErr >= 0);
   
   // close file
   dn_fs_close(configFileHandle);
}

//===== lock

// data

void lockData() {
   INT8U      osErr;
   
   OSSemPend(synctemp_v.dataLock, 0, &osErr);
   ASSERT(osErr == OS_ERR_NONE);
}

void unlockData() {
   OSSemPost(synctemp_v.dataLock);
}

// rxPacket

void lockRxPk() {
   INT8U      osErr;
   
   OSSemPend(synctemp_v.rxPkLock, 0, &osErr);
   ASSERT(osErr == OS_ERR_NONE);
}

void unlockRxPk() {
   OSSemPost(synctemp_v.rxPkLock);
}

//=============================================================================
//=========================== install a kernel header =========================
//=============================================================================

/**
A kernel header is a set of bytes prepended to the actual binary image of this
application. This header is needed for your application to start running.
*/

DN_CREATE_EXE_HDR(DN_VENDOR_ID_NOT_SET,
                  DN_APP_ID_NOT_SET,
                  VER_MAJOR,
                  VER_MINOR,
                  VER_PATCH,
                  VER_BUILD);
