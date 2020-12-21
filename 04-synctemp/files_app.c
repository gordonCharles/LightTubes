/*
Copyright (c) 2013, Dust Networks.  All rights reserved.
*/

// SDK includes
#include "dn_common.h"
#include "cli_task.h"
#include "loc_task.h"
#include "dn_gpio.h"
#include "dn_system.h"
#include "dn_exe_hdr.h"
#include "dn_fs.h"
#include "dn_flash_drv.h"
#include "dn_time.h"
#include "Ver.h"

// app includes
#include "app_task_cfg.h"

// C includes
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>   // for isalnum()

//=========================== defines =========================================
#define  VARIETIES                 25
#define  MAX_FILE_SIZE             128
#define  MAX_FRUIT_SIZE            12
#define  NULL_TERM                  1

// for speed test
#define  US_PER_TICK               30
#define  TEST_FILE_SIZE            2048
#define  BLOCK_SIZE                128

//=========================== prototypes ======================================
//====tasks
static void filesTask(void* unused);

//===== CLI handlers
dn_error_t cli_displayFS(const char* arg, INT32U len);   // display current filesystem properties
dn_error_t cli_reset(const char* arg, INT32U len);       // reset the mote. This will clear temp files
dn_error_t cli_open(const char* arg, INT32U len);        // open an existing file or create a new one
dn_error_t cli_close(const char* arg, INT32U len);       // close an open file
dn_error_t cli_delete(const char* arg, INT32U len);      // delete a file
dn_error_t cli_write(const char* arg, INT32U len);       // write dummy data to a file
dn_error_t cli_read(const char* arg, INT32U len);        // read a file
dn_error_t cli_append(const char* arg, INT32U len);      // append dummy data to a file - only works with shadowed files
dn_error_t cli_speed(const char* arg, INT32U len);       // r/w speed test

//==== helpers
void printStr(char* buf, INT8U len);

//=========================== variables =======================================

// Variables local to this application.
typedef struct {
   OS_STK       filesTaskStack[TASK_APP_FILES_STK_SIZE];
   char         data[MAX_FILE_SIZE];
} app_v_t;

app_v_t app_v;

//=========================== const  ==============================================
const dnm_ucli_cmdDef_t cliCmdDefs[] = {
  {&cli_reset,                "reset",        "reset",                          DN_CLI_ACCESS_LOGIN }, 
  {&cli_displayFS,            "display",      "display",                        DN_CLI_ACCESS_LOGIN },
  {&cli_open,                 "open",         "open <filename> [-s | -t]",      DN_CLI_ACCESS_LOGIN }, 
  {&cli_close,                "close",        "close <filename>",               DN_CLI_ACCESS_LOGIN }, 
  {&cli_delete,               "delete",       "delete <filename>",              DN_CLI_ACCESS_LOGIN }, 
  {&cli_write,                "write",        "write <filename>",               DN_CLI_ACCESS_LOGIN },
  {&cli_read,                 "read",         "read <filename>",                DN_CLI_ACCESS_LOGIN },
  {&cli_append,               "append",       "append <filename>",              DN_CLI_ACCESS_LOGIN },
  {&cli_speed,                "speed",        "speed",                          DN_CLI_ACCESS_LOGIN },
  {NULL,                       NULL,           NULL,                            DN_CLI_ACCESS_NONE  },
};

const char* dummyData[] = {
   "apple", "pear", "grape", "mango", "banana", "pineapple", "plum", "tangerine", "peach", "watermelon", 
   "strawberry", "apricot", "blackberry", "cherry", "dragonfruit", "grapefruit", "guava", "kiwi", "orange", "nectarine", 
   "papaya", "blueberry", "rambutan", "quince", "pomegranate"
};
//=========================== initialization ==================================

/**
\brief This is the entry point for the application code.
*/
int p2_init(void) {
   INT8U                  osErr;
   
   //===== initialize helper tasks
   
   // CLI task
   cli_task_init(
      "Files",                              // appName
      cliCmdDefs                            // cliCmds
   );
   
   // local interface task
   loc_task_init(
      JOIN_NO,                             // fJoin
      NETID_NONE,                           // netId
      UDPPORT_NONE,                         // udpPort
      NULL,                                 // joinedSem
      BANDWIDTH_NONE,                       // bandwidth
      NULL                                  // serviceSem
   );
   
    //===== files task 
   osErr = OSTaskCreateExt(
      filesTask,
      (void *) 0,
      (OS_STK*) (&app_v.filesTaskStack[TASK_APP_FILES_STK_SIZE-1]),
      TASK_APP_FILES_PRIORITY,
      TASK_APP_FILES_PRIORITY,
      (OS_STK*) app_v.filesTaskStack,
      TASK_APP_FILES_STK_SIZE,
      (void *) 0,
      OS_TASK_OPT_STK_CHK | OS_TASK_OPT_STK_CLR
   );
   ASSERT(osErr == OS_ERR_NONE);
   OSTaskNameSet(TASK_APP_FILES_PRIORITY, (INT8U*)TASK_APP_FILES_NAME, &osErr);
   ASSERT(osErr == OS_ERR_NONE);
   
   return osErr;
}

//=========================== CLI handlers ====================================

//===== reset
dn_error_t cli_reset(const char* arg, INT32U len) {
   INT8U      rc;
   
   dnm_ucli_printf("Resetting...\r\n\n");
   
   // send reset to stack
   dnm_loc_resetCmd(&rc);
   ASSERT(rc == DN_API_RC_OK);
   
   return DN_ERR_NONE;
}
//===== display info about the filesystem
dn_error_t cli_displayFS(const char* arg, INT32U len) {
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

// Open an existing file or create a new one and open it.  The file is opened with a maxLen=128 bytes. 
//     Non-shadowed files are limited to one 2048-byte page. 
//     Shadowed files can be stored in a single sector if maxLen <2028, but cannot be appended to exceed that length.
//     If a shadowed file is opened with maxLen >= 2028, it can be appended to exceed that length.  
dn_error_t cli_open(const char* arg, INT32U len){
   dn_fs_handle_t  fileHandle;
   int             length;
   INT8U           nameStr[12];
   char            modeSwitch = 0;
   INT8U           mode;
      
   //--- parse filename and any mode switches
   length = sscanf(arg, "%12s -%c", nameStr, &modeSwitch);
   if ((length < 1) || (nameStr[0] != '2')){
      dnm_ucli_printf("Usage: open <filename> [-s | -t] - see dustcloud documentation for naming rules\r\n");   
      return DN_ERR_NONE;
   }
      
   if (modeSwitch == 't'){
      mode = DN_FS_MODE_TEMP;  // temp files are deleted upon reset
   }
   else if (modeSwitch == 's'){
      mode = DN_FS_MODE_SHADOW;  // shadowed files are fault tolerant but take more space
   }
   else{
      mode = DN_FS_MODE_OTH_RW;  // read/write file
   }
      
   fileHandle = dn_fs_find(nameStr);
   if(fileHandle > 0){
      dnm_ucli_printf("%s already exists\r\n", nameStr);
   }    
   else{
      dnm_ucli_printf("%s does not exist. Creating it....\r\n", nameStr, (void *)fileHandle);
   }
      
   fileHandle = dn_fs_open(
                                 nameStr,
                                 DN_FS_OPT_CREATE,
                                 MAX_FILE_SIZE,
                                 mode
   );
      
   if (fileHandle > 0){
      dnm_ucli_printf("Opened %s\r\n", nameStr);
      return DN_ERR_NONE;
   }
      
   switch (fileHandle){
      case DN_ERR_INVALID:
         dnm_ucli_printf("Invalid filename - see documentation on naming rules\r\n");
      break;
      case DN_ERR_NO_RESOURCES:
         dnm_ucli_printf("No space to create file\r\n");
      break;
         case DN_ERR_NONE:
         case DN_ERR_ERROR:
             dnm_ucli_printf("Error creating or opening file\r\n");
         break;
      }
      
      return DN_ERR_NONE;
}

// Close a file. Closing a file is optional, but closed files cannot be written to.
dn_error_t cli_close(const char* arg, INT32U len){
   dn_fs_handle_t  fileHandle;
   int             length;
   INT8U           nameStr[12];
 
   //--- parse filename
   length = sscanf(arg, "%12s ", nameStr);
   if (length < 1){
      dnm_ucli_printf("Usage: delete <filename>\r\n");   
      return DN_ERR_NONE;
   }
   
   fileHandle = dn_fs_find(nameStr);
   if(fileHandle <= DN_ERR_NONE){
      dnm_ucli_printf("Could not close %s", nameStr);
      return (DN_ERR_NONE);
   }
   else{
      dn_fs_close(fileHandle);
      return (DN_ERR_NONE);
   }
}
// Delete an existing file
dn_error_t cli_delete(const char* arg, INT32U len){
   dn_error_t      dnErr;  
   int             length;
   INT8U           nameStr[12];
      
   //--- parse filename
      length = sscanf(arg, "%12s ", nameStr);
      if (length < 1){
         dnm_ucli_printf("Usage: delete <filename>\r\n");   
         return DN_ERR_NONE;
      }
   
      dnErr = dn_fs_delete(nameStr);
      
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
      }
      
      return (DN_ERR_NONE);  
}

// Write a string to a file
dn_error_t cli_write(const char* arg, INT32U len){
   dn_error_t           dnErr;
   dn_fs_handle_t       fileHandle;
   dn_fs_fileinfo_t     fileInfo;
   int                  length;
   INT8U                nameStr[12];
   INT8U                index;
   
   //--- parse filename
   length = sscanf(arg, "%12s", nameStr);
   if ((length < 1) || (nameStr[0] != '2')){
      dnm_ucli_printf("Usage: write <filename>\r\n");   
      return DN_ERR_NONE;
   }
    
   memset(app_v.data, ' ', MAX_FRUIT_SIZE);
   index = rand() % VARIETIES;
      
   fileHandle = dn_fs_find(nameStr);
   if (fileHandle < DN_ERR_NONE){
       dnm_ucli_printf("%s does not exist or isn't open\r\n", nameStr);
       return (DN_ERR_NONE);
   } 
  
   // get file info
   dnErr = dn_fs_getFileInfo(fileHandle, &fileInfo);
   if(dnErr != DN_ERR_NONE){
      dnm_ucli_printf("Error getting file info!\r\n");
      return (DN_ERR_NONE);
   }
   
   if(fileInfo.mode == DN_FS_MODE_SHADOW){
      strcpy(app_v.data, dummyData[index]);
      length = strlen(app_v.data);
   }
   else{
      // pad to word boundary with spaces
      memcpy(app_v.data, dummyData[index], strlen(dummyData[index]));
      length = strlen(dummyData[index]);
      length += 4 - (length % 4); 
   }
   
   //write the file
   dnErr = dn_fs_write(
                  fileHandle,
                  0L,
                  (INT8U*) app_v.data,
                  (INT8U) length
   );
   
   if(dnErr < DN_ERR_NONE){
      dnm_ucli_printf("Error %d writing file\r\n", dnErr);
      if (dnErr == DN_ERR_NOT_EMPTY) {
            dnm_ucli_printf("Cannot overwrite used portion of non-shadowed file - try appending\r\n", dnErr);
         }
      }
      else{
         dnm_ucli_printf("Writing %s (%s%d bytes)\r\n", dummyData[index], (fileInfo.mode==DN_FS_MODE_SHADOW)?"":"padded to ", length);
      }
   
   return (DN_ERR_NONE);
}

// Read a file
dn_error_t cli_read(const char* arg, INT32U len){
   dn_error_t           dnErr;
   dn_fs_handle_t       fileHandle;
   dn_fs_fileinfo_t     fileInfo;
   int                  length;
   INT8U                nameStr[12];
   INT8U                i;
   
   //--- parse filename
   length = sscanf(arg, "%12s", nameStr);
   if ((length < 1) || (nameStr[0] != '2')){
      dnm_ucli_printf("Usage: read <filename>\r\n");   
      return DN_ERR_NONE;
   }
   
   // get file handle
   fileHandle = dn_fs_find(nameStr);
   if (fileHandle < DN_ERR_NONE){
       dnm_ucli_printf("%s does not exist or isn't open\r\n", nameStr);
       return (DN_ERR_NONE);
   } 
   
   // get file info
   dnErr = dn_fs_getFileInfo(fileHandle, &fileInfo);
    if(dnErr != DN_ERR_NONE){
      dnm_ucli_printf("Error getting file info!\r\n");
      return (DN_ERR_NONE);
   }
   
   if(fileInfo.len == 0){
      dnm_ucli_printf("%s is empty\r\n", nameStr);
      return (DN_ERR_NONE);
   }
   
   // for shadowed files, fileInfo.len is the size of the used part of the file. 
   // For non-shadowed files, fileInfo.len is the maximum size of the file.
   memset(app_v.data, 0xFF, MAX_FILE_SIZE);
   dnErr = dn_fs_read(
                  fileHandle,
                  0L,
                  (INT8U*) app_v.data,
                  fileInfo.len
   );
   
   if(dnErr < DN_ERR_NONE){
         dnm_ucli_printf("Error %d reading %s\r\n", dnErr, nameStr);
   }
   else if(app_v.data[0] == 0xFF) {
         dnm_ucli_printf("%s is empty\r\n", nameStr);   
   }
   else {
      dnm_ucli_printf("%s contains '", nameStr);
      if(fileInfo.mode == DN_FS_MODE_SHADOW){
         for(i=0;i<fileInfo.len;i++){
            dnm_ucli_printf("%c", app_v.data[i]);
         }
         dnm_ucli_printf("' (%d bytes)\r\n", fileInfo.len-1);
      }
      else{
         i = 0;
         while(app_v.data[i] != 0xFF){
            dnm_ucli_printf("%c", app_v.data[i]);
            i++;
         }   
         dnm_ucli_printf("' (%d bytes)\r\n", i);
      }
   }
   
   return (DN_ERR_NONE);
}

// append data to a file
dn_error_t cli_append(const char* arg, INT32U len){
   dn_error_t           dnErr;
   dn_fs_handle_t       fileHandle;
   dn_fs_fileinfo_t     fileInfo;
   int                  length;
   INT8U                offset;
   INT8U                nameStr[12];
   INT8U                index;
   
   // --- read filename
   length = sscanf(arg, "%12s", nameStr);
   if ((length < 1) || (nameStr[0] != '2')){
      dnm_ucli_printf("Usage: append <filename>\r\n");   
      return DN_ERR_NONE;
   }
   
   //get file handle
   fileHandle = dn_fs_find(nameStr);
   if(fileHandle < DN_ERR_NONE){
      dnm_ucli_printf("That file does not exist or isn't open\r\n");
      return (DN_ERR_NONE);
   }
   
   dnErr = dn_fs_getFileInfo(fileHandle, &fileInfo);
   if(dnErr != DN_ERR_NONE){
      dnm_ucli_printf("Error getting file info!\r\n");
      return (DN_ERR_NONE);
   }
    
   if(fileInfo.mode == DN_FS_MODE_SHADOW){
      // can append anywhere
      offset = fileInfo.len;  // can append anywhere
   }
   else {
      // need to know where file content ends
      memset(app_v.data, 0xFF, MAX_FILE_SIZE);
      dnErr = dn_fs_read(
                  fileHandle,
                  0L,
                  (INT8U*) app_v.data,
                  fileInfo.len
      );
       
      if(dnErr < DN_ERR_NONE){
         dnm_ucli_printf("Error %d reading %s\r\n", dnErr, nameStr);
      }
      
      // can only append on word boundary
      offset = 0;
      while(app_v.data[offset] != 0xFF){
         offset ++;
      }
   }
   
   memset(app_v.data, ' ', MAX_FRUIT_SIZE);
   index = rand() % VARIETIES;
   
   if(fileInfo.mode == DN_FS_MODE_SHADOW){
      strcpy(app_v.data, dummyData[index]);
      length = strlen(app_v.data);
   }
   else{
      // pad to word boundary with spaces
      memcpy(app_v.data, dummyData[index], strlen(dummyData[index]));
      length = strlen(dummyData[index]);
      length += 4 - (length % 4); 
   }
            
   dnErr = dn_fs_write(
                  fileHandle,
                  offset,
                  (INT8U*) app_v.data,
                  (INT8U) length
   );
   
   if(dnErr < DN_ERR_NONE){
         dnm_ucli_printf("Error %d appending %s\r\n", dnErr, nameStr);
   }
   else{   
      dnm_ucli_printf("Appending %s (%s%d bytes) to %s at offset %d\r\n", dummyData[index], 
                      (fileInfo.mode==DN_FS_MODE_SHADOW)?"":"padded to ", length, nameStr, offset);
   }

   return (DN_ERR_NONE);
}

dn_error_t cli_speed(const char* arg, INT32U len) {
   INT64U               start;
   INT64U               end;
   static INT32U        delta;
   dn_fs_handle_t       fileHandle;
   INT8U                i;
   
   // not checking for file errors
   
   memset(app_v.data, 0xA5, BLOCK_SIZE);
   
   // =======  regular file
   dnm_ucli_printf("Opening %d-byte file for test\r\n", TEST_FILE_SIZE);
   fileHandle = dn_fs_open(
                              "2test.tmp",
                              DN_FS_OPT_CREATE,
                              TEST_FILE_SIZE,
                              DN_FS_MODE_TEMP
   );
  
   // write test
   dnm_ucli_printf("Starting write test...\r\n");
   dn_getSystemTime(&start);
   for(i=0; i<TEST_FILE_SIZE/BLOCK_SIZE; i++){
      dn_fs_write(
                  fileHandle,
                  i*BLOCK_SIZE,
                  (INT8U*) app_v.data,
                  BLOCK_SIZE
      );
   }
   
   dn_getSystemTime(&end);
   delta = (1000 * (end - start)) / TIMER_TICKS_PER_SEC;
  // dnm_ucli_printf("Writing %dx %d-byte blocks took %ld ms\r\n", TEST_FILE_SIZE/BLOCK_SIZE, BLOCK_SIZE, delta);
   dnm_ucli_printf("Writing %d-byte blocks took %ld ms\r\n", BLOCK_SIZE, delta);
   
   //read test
   dnm_ucli_printf("Starting read test...\r\n");
   dn_getSystemTime(&start);
   for(i=0; i<TEST_FILE_SIZE/BLOCK_SIZE; i++){
      dn_fs_read(
                  fileHandle,
                  i*BLOCK_SIZE,
                  (INT8U*) app_v.data,
                  BLOCK_SIZE
      );
   }
  
   dn_getSystemTime(&end);
   delta = (1000000 * (end - start)) / TIMER_TICKS_PER_SEC;
   dnm_ucli_printf("Reading took %ld us\r\n", delta);
   
   dnm_ucli_printf("\r\n");
   dn_fs_deleteTmpFiles();    
   
   // =======  shadowed file
   dnm_ucli_printf("Opening %d-byte shadowed file for test...\r\n", TEST_FILE_SIZE);  
   fileHandle = dn_fs_open(
                              "2test.tmp",
                              DN_FS_OPT_CREATE,
                              TEST_FILE_SIZE,
                              DN_FS_MODE_SHADOW
   );
  
   // write test
   dnm_ucli_printf("Starting write test...\r\n");
   dn_getSystemTime(&start);
   for(i=0; i<TEST_FILE_SIZE/BLOCK_SIZE; i++){
      dn_fs_write(
                  fileHandle,
                  i*BLOCK_SIZE,
                  (INT8U*) app_v.data,
                  BLOCK_SIZE
      );
   }
  
   dn_getSystemTime(&end);
   delta = (1000 * (end - start)) / TIMER_TICKS_PER_SEC;
   dnm_ucli_printf("Writing %d-byte blocks took %ld ms\r\n", BLOCK_SIZE, delta);
   
   //read test
   dnm_ucli_printf("Starting read test...\r\n");
   dn_getSystemTime(&start);
   for(i=0; i<TEST_FILE_SIZE/BLOCK_SIZE; i++){
      dn_fs_read(
                  fileHandle,
                  i*BLOCK_SIZE,
                  (INT8U*) app_v.data,
                  BLOCK_SIZE
      );
   }
   
   dn_getSystemTime(&end);
   delta = (1000000 * (end - start)) / TIMER_TICKS_PER_SEC;
   dnm_ucli_printf("Reading took %ld us\r\n", delta);
   
   dnm_ucli_printf("\r\n");
   dn_fs_delete("2test.tmp"); 
   
   return (DN_ERR_NONE);
}
  
//=========================== files task ================================
static void filesTask(void* unused) {
//   dn_fs_fsinfo_t       info;
//   dn_error_t           dnErr;
//   INT8U                maxFiles;
//   dn_fs_handle_t       fileHdl;
//   INT32S               index;
//   dn_fs_fileinfo_t     fileInfo;
   INT64U               sysTime;
   
   OSTimeDly(1 * SECOND); // give stack banner time to print
   
   dn_getSystemTime(&sysTime);
   // seed the RNG
   srand((INT32U) sysTime);
/*     
   dnm_ucli_printf("\nList of currently stored files:\r\n");
   dnm_ucli_printf("   Name            Size Mode\r\n");
   
   dnErr = dn_fs_getFSInfo(&info);
   maxFiles = info.maxNumOfFiles;
   
   for(index = 0; index<maxFiles; index++){
      fileHdl = dn_fs_findByIdx(index);
      if (fileHdl > 0){
         dnErr = dn_fs_getFileInfo(fileHdl, &fileInfo);
         if (dnErr == DN_ERR_NONE){
            dnm_ucli_printf("   ");
            printStr(fileInfo.name, DN_FS_FILENAME_SIZE+1); 
            dnm_ucli_printf(" %6d", fileInfo.len);
            if(fileInfo.mode == DN_FS_MODE_TEMP) {
               dnm_ucli_printf(" temp\r\n", fileInfo.len);
            }
            else if(fileInfo.mode == DN_FS_MODE_SHADOW)  {
               dnm_ucli_printf(" shadow\r\n");
            }
            else{
               dnm_ucli_printf("\r\n");
            }
         }
      }
   } 
*/    
   while (1) { // this is a task, it executes forever

      // block the task for some time
      OSTimeDly(1 * SECOND);
   }
}
                            
//-------- helpers

void printStr(char* buf, INT8U len) {
   INT8U i;
   
   for (i=0;i<len;i++) {
      if(isalnum(buf[i]) || buf[i] == '.')
         dnm_ucli_printf("%c", buf[i]);
      else
         dnm_ucli_printf(" ");
   }
}

//=============================================================================
//=========================== install a kernel header =========================
//=============================================================================

/**
A kernel header is a set of dnErr prepended to the actual binary image of this
application. This header is needed for your application to start running.
*/

DN_CREATE_EXE_HDR(DN_VENDOR_ID_NOT_SET,
                  DN_APP_ID_NOT_SET,
                  VER_MAJOR,
                  VER_MINOR,
                  VER_PATCH,
                  VER_BUILD);
