/*
This application is designed to work with a DTMF detectector connected to the TIMEn pin of the LTP5901 / LTC5800.
The application detects activity on the TIMEn pin, looking for a sequence of 4 consecutive pulses 200ms apart from
each other.  The average value of the pulses is taken assuming exactly 200ms between pulses to filter noise and 
provide an timestamp for the pulses to with in a few uS.  A "REPORT_TIME" packet is sent to the network manager
once the timestamp is calculated.
*/

// OCSDK includes
#include "dn_common.h"
#include "dnm_local.h"
#include "cli_task.h"
#include "loc_task.h"
#include "dn_time.h"
#include "dn_exe_hdr.h"
#include "Ver.h"

//C includes
#include <inttypes.h>
#include <string.h>

// App includes
#include "app_task_cfg.h"

//=========================== defines =========================================

#define LED_APP_PORT         0xF0BA
#define LOOP_PERIOD          250
#define FIFO_DEPTH           4
#define FIFO_END             FIFO_DEPTH - 1
#define REPORT_TIME          0x0F  // Report Time Command ID

//=========================== Join defines ====================================
#define HI_DUTY            255
#define LOW_DUTY           5
#define HI_TIMEOUT         15 * SECOND   // 2x average sync time at 100%, so if a manager is in range we'll likely hear it
#define LOW_TIMEOUT        150 * SECOND  // Average sync time to manager at 5%
#define IDLE_TIMEOUT       30 * SECOND   // If we don't hear at either two, might want to wait a lot longer

//=========================== variables =======================================

typedef struct {
   OS_STK                    timeTaskStack[TASK_APP_TIME_STK_SIZE];
   dn_time_asn_t             currentASN;
   dn_time_utc_t             currentUTC;
   INT64U                    sysTime;
   dn_api_loc_notif_time_t   timeNotif;
} time_app_vars_t;

typedef struct {
   OS_EVENT*       joinedSem;
   OS_STK          joinTaskStack[TASK_APP_JOIN_STK_SIZE];
} join_app_vars_t;

join_app_vars_t join_app_vars;

PACKED_START

typedef struct {
   INT32U                    S;
   INT32U                    uS;
} time_t;

typedef struct{
   INT8U  cmdId;             // command identifier
   INT8U  payload[];         // payload
} time_payload_ht;

PACKED_STOP

time_app_vars_t time_app_vars;

INT32U                      utcSecondsFifo[FIFO_DEPTH];
INT32U                      utcuSecondsFifo[FIFO_DEPTH];
INT32U                      lastMarkerSeconds;
INT32U                      lastMarkeruSeconds;

INT8U                       timenPinActive;

OS_EVENT*                 fakeJoin;  
OS_EVENT*                 timeAppJoin;

//=========================== prototypes ======================================

static void timeTask(void* unused);
static void joinTask(void* unused);
dn_error_t timeNotifCb(dn_api_loc_notif_time_t* timeNotif, INT8U length);

//=========================== initialization ==================================

/**
\brief This is the entry point for the application code.
*/
int p2_init(void) {
   INT8U           osErr;
   
   
   timeAppJoin = OSSemCreate(0);                  // NOT joined by default
   ASSERT(timeAppJoin!=NULL);
   
   fakeJoin = OSSemCreate(0);                  // NOT joined by default
   ASSERT(fakeJoin!=NULL);

   
   //===== initialize helper tasks
   
   cli_task_init(
      "time",                               // appName
      NULL                                  // cliCmds
   );
   
   loc_task_init(
      JOIN_NO,                              // fJoin
      NULL,                                 // netId
      LED_APP_PORT,                         // udpPort - share port with LED Tubes
      timeAppJoin,                          // joinedSem
      500,                                  // 500 ms reporting rate 
      NULL                                  // serviceSem
   );
   
   //==== register a callback for when receiving a time notification   
   dnm_loc_registerTimeNotifCallback(timeNotifCb);
   
   //===== initialize timeTask
   osErr = OSTaskCreateExt(
      timeTask,
      (void *) 0,
      (OS_STK*) (&time_app_vars.timeTaskStack[TASK_APP_TIME_STK_SIZE - 1]),
      TASK_APP_TIME_PRIORITY,
      TASK_APP_TIME_PRIORITY,
      (OS_STK*) time_app_vars.timeTaskStack,
      TASK_APP_TIME_STK_SIZE,
      (void *) 0,
      OS_TASK_OPT_STK_CHK | OS_TASK_OPT_STK_CLR
   );
   ASSERT(osErr==OS_ERR_NONE);
   OSTaskNameSet(TASK_APP_TIME_PRIORITY, (INT8U*)TASK_APP_TIME_NAME, &osErr);
   ASSERT(osErr==OS_ERR_NONE);
   
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
   OSTimeDly(5 * SECOND);
   
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
         OSSemPend(timeAppJoin, HI_TIMEOUT, &osErr);
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

static void timeTask(void* unused) {
INT8U    i;
INT32U   deltaT;
INT32U   nowS;
INT32U   nowuS;
time_t   avgTime;
INT32U   deltaTimen;
INT32U   baseTimeuS;
INT32U   baseTimeS;

   INT8U                dnErr;
   loc_sendtoNW_t*      pkToSend;
   time_payload_ht*     payloadToSend;
   INT8U                rc;
   INT8U                pkBuf[sizeof(loc_sendtoNW_t) + 20];

   timenPinActive = 0;
   deltaT = 0;
   //GIve stack time to print banner
   OSTimeDly(10 * SECOND);
   for (i=0;i<FIFO_DEPTH;i++) {
      utcSecondsFifo[i] = 0;
      utcuSecondsFifo[i] = 0;
   }
   
   while (1) { // this is a task, it executes forever
     
      // network time
      dn_getNetworkTime(
         &time_app_vars.currentASN,
         &time_app_vars.currentUTC
      );
      
      nowS  = (INT32U)time_app_vars.currentUTC.sec;
      nowuS = (INT32U)time_app_vars.currentUTC.usec;
      
      if (timenPinActive == 1) {
        if ((nowS - utcSecondsFifo[0]) > 1) {  // Waiting for four pusles, 200ms apart, resetting to avoid spurious pulse corrupting FIFO 
           dnm_ucli_printf("Error current time more than 1 second after TIMEn pin strobe.\r\n");
        } else {
           deltaT = (nowS - utcSecondsFifo[0]) * 1000000 + nowuS - utcuSecondsFifo[0];
        }
        if (deltaT > 300000) {  // Wait until we've had more than 200ms + margin from the last pulse - then we are ready to compute the average
           timenPinActive = 0;
           if (((utcSecondsFifo[0] - utcSecondsFifo[FIFO_END])*1000000 + utcuSecondsFifo[0] - utcuSecondsFifo[FIFO_END]) > (200000 * FIFO_END+100000)) {
              dnm_ucli_printf("Time Strobe FIFO Not fully filled.\r\n");  // Failed check for four pulses in 700ms
           } else {
              deltaTimen = 0;
              baseTimeS  = utcSecondsFifo[FIFO_END];
              baseTimeuS = utcuSecondsFifo[FIFO_END];
              // Average is calculated as [(first - last) + (second+200ms - last) + (third+400ms - last)]/4 + last to avoid negative results
              for (i=0;i<FIFO_END;i++) {  
                 if ((utcSecondsFifo[i] - utcSecondsFifo[FIFO_END]) > 0) {
                    deltaTimen = deltaTimen + (1000000 + utcuSecondsFifo[i] + (FIFO_END-i)*200000) - utcuSecondsFifo[FIFO_END];
                 } else {
                    deltaTimen = deltaTimen + utcuSecondsFifo[i]-utcuSecondsFifo[FIFO_END]+(FIFO_END-i)*200000;
                 }
              }
              deltaTimen = deltaTimen >> 2;
              avgTime.uS = baseTimeuS + deltaTimen;
              if (avgTime.uS > 1000000) {
                 avgTime.S = baseTimeS + 1;
                 avgTime.uS = avgTime.uS - 1000000;
              } else {
                 avgTime.S = baseTimeS;
              }
              
              // note that printing INT64S and INT64U doesn't work using %lld formatter - casting allows
              // printing but will eventually overflow

              dnm_ucli_printf(" - average utc seconds:      %ld s\r\n", avgTime.S);
              dnm_ucli_printf(" - average utc microseconds: %ld us\r\n", avgTime.uS);
              
                    // fill in packet metadata
              pkToSend = (loc_sendtoNW_t*)pkBuf;
              pkToSend->locSendTo.socketId          = loc_getSocketId();
              pkToSend->locSendTo.destAddr          = DN_MGR_IPV6_MULTICAST_ADDR;
              pkToSend->locSendTo.destPort          = LED_APP_PORT;
              pkToSend->locSendTo.serviceType       = DN_API_SERVICE_TYPE_BW;   
              pkToSend->locSendTo.priority          = DN_API_PRIORITY_MED;   
              pkToSend->locSendTo.packetId          = 0xFFFF;
      
              // fill in packet payload
              payloadToSend = (time_payload_ht*)pkToSend->locSendTo.payload;
              payloadToSend->cmdId                  = REPORT_TIME;
              avgTime.S                             = htonl(avgTime.S);
              avgTime.uS                            = htonl(avgTime.uS);
              memcpy(payloadToSend->payload,&avgTime,sizeof(time_t));
      
              // send packet
              dnErr = dnm_loc_sendtoCmd(
                 pkToSend,
                 sizeof(time_payload_ht)+sizeof(time_t)+2,
                 &rc
              );
              ASSERT (dnErr == DN_ERR_NONE);
              if (rc!=DN_ERR_NONE){
                 dnm_ucli_printf("ERROR sending data (RC=%d)\r\n", rc);
              }

          }

        }
      }

      // wait more than the TIMEn pulse period
      OSTimeDly(LOOP_PERIOD);
   }
}

dn_error_t timeNotifCb(dn_api_loc_notif_time_t* timeNotif, INT8U length) {
   INT8U           i;
   
   ASSERT(length==sizeof(dn_api_loc_notif_time_t));
   // Note that  dn_api_loc_notif_time_t contains a field
   //     dn_utc_time_t   utcTime;
   // contrast this with the fields returned by dn_getNetworkTime
   //     dn_time_utc_t  currentUTC;
   // the contents of the two utc time structures are identical, but the stack
   // uses the two types in different layers.
   
   // copy notification to global variables for simpler debugging
   // notification fields other than ASN are in network order, so must be swapped for use
   time_app_vars.timeNotif.upTime = ntohl(timeNotif->upTime);
   memcpy(&time_app_vars.timeNotif.asn, &timeNotif->asn, sizeof(dn_asn_t));
   time_app_vars.timeNotif.offset = ntohs(timeNotif->offset);
   time_app_vars.timeNotif.asnSubOffset = ntohs(timeNotif->asnSubOffset);
   time_app_vars.timeNotif.utcTime.seconds = ntohll(timeNotif->utcTime.seconds);
   time_app_vars.timeNotif.utcTime.useconds = ntohl(timeNotif->utcTime.useconds);
   
   dnm_ucli_printf("time notification:\r\n");
   dnm_ucli_printf(" - ASN:              0x");
   for (i=0;i<sizeof(time_app_vars.timeNotif.asn);i++) {
      dnm_ucli_printf("%02x",time_app_vars.timeNotif.asn.byte[i]);
   }
   dnm_ucli_printf("\r\n");
   dnm_ucli_printf(" - offset:           %d us\r\n",time_app_vars.timeNotif.offset);
   dnm_ucli_printf(" - utc seconds:      %d s\r\n",(INT32U) time_app_vars.timeNotif.utcTime.seconds);
   dnm_ucli_printf(" - utc microseconds: %d us\r\n",(INT32U) time_app_vars.timeNotif.utcTime.useconds);
   // uptime is only nonzero after join
   dnm_ucli_printf(" - upTime:           %ld s (%ld 32KHz ticks)r\n",time_app_vars.timeNotif.upTime, 
                                         time_app_vars.timeNotif.upTime * 32768);
   dnm_ucli_printf("\r\n");
   
   // shift values into FIFO for averaging after four pulses have been received in less than 700ms
   for (i=FIFO_END;i>0;i--) {
      utcSecondsFifo[i] = utcSecondsFifo[i-1];
      utcuSecondsFifo[i] = utcuSecondsFifo[i-1];
   }   
   utcSecondsFifo[0] = (INT32U) time_app_vars.timeNotif.utcTime.seconds;
   utcuSecondsFifo[0] = (INT32U) time_app_vars.timeNotif.utcTime.useconds;
   timenPinActive = 1;
   
   return DN_ERR_NONE;
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
