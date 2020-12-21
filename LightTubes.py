#!/usr/bin/python
# Developed on python 2.7.5
'''
This application provides a visual editor for generting spatial and temporal sequences of colors on custom
designed hardware based on the SmartMesh IP protocol and the LTC5800 mesh networking SoC.  The built in 
time management of both the protocol and the hardware allow for synchronized execution of multiple instances
of an application running on the LTC5800 SoC.  In addition to providing the application specific editor 
needed to practically manage the volume of information needed to create the "lighting art" the application
provides a simplified interface to the network and controls required to program the the lighting sequences
into the custom hardware and to control the music / lighting timing for rehearsal and performance.  The 
application also includes utilities to monitor the network and creating virtual to physical mapping of the
custom designed hardware, or LightTubes, supporting a method of redundancy required to ensure reliable 
operation during a live performance.

'''
#============================ adjust path =====================================

import sys
import os
import struct
import codecs
import string
if __name__ == "__main__":
    here = sys.path[0]
    sys.path.insert(0, os.path.join(here, 'libs'))
    sys.path.insert(0, os.path.join(here, 'external_libs'))

#============================ imports =========================================

import urllib3
import traceback
import time
import base64
import threading
import pyaudio
import wave

# generic SmartMeshSDK imports
from SmartMeshSDK                      import sdk_version
from SmartMeshSDK.protocols.oap        import OAPDispatcher, \
                                              OAPClient,     \
                                              OAPMessage,    \
                                              OAPNotif
# VManager-specific imports
from VManagerSDK.vmanager              import Configuration
from VManagerSDK.vmgrapi               import VManagerApi
from VManagerSDK.vmanager.rest         import ApiException
from VManagerSDK.vmanager              import DataPacketSendInfo

#============================ defines =========================================

from random import randint
from time import sleep

import imp, re, numpy
#import os
#import sys

def main_is_frozen():
    return (hasattr(sys, "frozen") or # new py2exe
            hasattr(sys, "importers") # old py2exe
            or imp.is_frozen("__main__")) # tools/freeze

# in dev mode, find the python mega-widgets library relative to this source
if sys.path[0]:
    sys.path.insert(0, os.path.join(sys.path[0], '..', 'Pmw.1.3.2', 'src'))

import Pmw

import Tkinter as tk
from tkFileDialog import askopenfilename, asksaveasfilename
from PIL import ImageTk, Image

import struct

#from Tkinter import *
#--import dmTxt2Html
#-- 
#import string
import traceback
import functools
import copy

develop        = 1

ProgramVersion = (1, 0)
VersionString  = '.'.join([str(v) for v in ProgramVersion])

# Version is the version of the table format written into flash
# Now overloaded to recognize Version > 1, support 12 songs versus 4 for Versions < 2
Version = 2

Canvas      = tk.Canvas
Frame       = tk.Frame
Label       = tk.Label
Checkbutton = tk.Checkbutton
Button      = tk.Button
StringVar   = tk.StringVar
IntVar      = tk.IntVar
Scrollbar   = tk.Scrollbar
Listbox     = tk.Listbox
Radiobutton = tk.Radiobutton
END         = tk.END
NW          = tk.NW
N           = tk.N
S           = tk.S
E           = tk.E
W           = tk.W
Entry       = tk.Entry
#-- dmTxt2Html.promo = "promo string" #-- string.replace(dmTxt2Html.promo, dmTxt2Html.cgi_home, '')

class AutoScrollbar(Scrollbar):
    # a scrollbar that hides itself if it's not needed.  only
    # works if you use the grid geometry manager.
    def set(self, lo, hi):
        if float(lo) <= 0.0 and float(hi) >= 1.0:
            # grid_remove is currently missing from Tkinter!
            self.tk.call("grid", "remove", self)
        else:
            self.grid()
        Scrollbar.set(self, lo, hi)
    def pack(self, **kw):
        raise TclError, "cannot use pack with this widget"
    def place(self, **kw):
        raise TclError, "cannot use place with this widget"

#-- Create some module scope global variables
root, menu_frame = (None, None)
canvas, util_frame, info_frame, mode_frame = (None, None, None, None)
vscrollbar = None

#============================ start of VManager Specific Code =================
#============================ defines =========================================

#DFLT_VMGR_HOST          = "127.0.0.1"
#DFLT_VMGR_HOST           = "192.168.1.77" # working as of June Show
DFLT_VMGR_HOST           = "192.168.1.91"
DFLT_MOTE_MAC            = "FF-FF-FF-FF-FF-FF-FF-FF"
BROADCAST_MOTE_MAC       = "FF-FF-FF-FF-FF-FF-FF-FF"
#TEST_MOTE_MAC            = "00-17-0D-00-00-58-59-1D"
MOTE14_MAC               = "00-17-0D-00-00-58-59-1D"
TEST_MOTE_MAC            = "00-17-0D-00-00-59-65-75"
DFLT_RATE                = 30000
DFLT_SIZE                = 60
PRIORITY                 = "low"

#LED_APP_PORT             = 61624
LED_APP_PORT             = 0xF0BA
PKT_SET_START_TIME       = 0x01
PKT_EXTERNAL_FLASH_ERASE = 0x02
PKT_EXTERNAL_FLASH_WRITE = 0x03
PKT_SONG_ERASE           = 0x04
PKT_SONG_APPEND          = 0x05
PKT_STOP                 = 0x06
PKT_SEND_SONG            = 0x07
PKT_SEND_SCENE           = 0x08
PKT_SEND_SHIFT           = 0x09
PKT_ENABLE_INIT_COLOR    = 0x0A
PKT_TURN_TO_BLACK        = 0x0B
PKT_EXTERNAL_FLASH_READ  = 0x0C
PKT_SONG_READ            = 0x0D
PKT_RESET_COM_COUNT      = 0x0E
PKT_REPORT_TIME          = 0x0F

LED_ACK                  = 0x01
LED_NAK                  = 0x02

NUM_SEND_SONG_RETRIES    = 3
NUM_ERASE_RETRIES        = 3
NUM_WRITE_RETRIES        = 3
ERASE_TIMEOUT            = 14  # ERASE TIMEOUT in # 10s intervals
WRITE_TIMEOUT            = 40  # WRITE TIMEOUT in seconds
SEND_SONG_TIMEOUT        = 10  # Send Song Timeout in 0.25s intervals
RESET_COM_COUNT_TIMEOUT  = 4   # WRITE TIMEOUT in seconds
NUM_STOP_RETRIES         = 3
STOP_TIMEOUT             = 4  # Stop Song Timeout in 0.25s intervals
PKT_REPEAT_DELAY         = 0.5 #Packet Repeat Delay in seconds

NETWORK_ON               = False

MAX_SONG_APPEND_LEN      = 74
RC_DATA_TOO_LONG         = 2
CLIP                     = 4


SCN_NUM_BYTES            = 120
PKT_NUM_BYTES            = 60
SCN_NUM_LEDS             = 30

# Start of song delay is 10s - 26ms, or 9974000 us
SOS_DELAY_S              = 9
SOS_DELAY_US             = 974000

urllib3.disable_warnings() # disable warnings that show up about self-signed certificates

#============================ variables =======================================

mote_exists = False
stop_event  = threading.Event()
'''
motes       = {"00-17-0D-00-00-58-59-1D" : {"Num" : 1, "state" : "operational", "ack" : {"SetStartTime" : 0, "EraseExternalFlash" : 0,
                    "ExternalFlashWrite" : 0, "SongErase" : 0, "SongAppend" : 0, "Stop" : 0, "SendSong" : 0, "SendScene" : 0, "SendShift" : 0,
                    "EnableInitColor" : 0, "TurnToBlack" : 0, "ExternalFlashRead" : 0, "SongRead" : 0, "ComCount" : 0, "StartSong" : 0, "StopSong" : 0}},
              }
              '''
motes       = {"00-17-0D-00-00-30-B2-6E" : {"state" : "operational", "ack" : {"SetStartTime" : 0, "EraseExternalFlash" : 0,
                       "ExternalFlashWrite" : 0, "SongErase" : 0, "SongAppend" : 0, "Stop" : 0, "SendSong" : 0, "SendScene" : 0, "SendShift" : 0,
                       "EnableInitColor" : 0, "TurnToBlack" : 0, "ExternalFlashRead" : 0, "SongRead" : 0, "ComCount" : 0, "StartSong" : 0, "StopSong" : 0}},
               "00-17-0D-00-00-30-B8-EE" : {"state" : "operational", "ack" : {"SetStartTime" : 0, "EraseExternalFlash" : 0,
                       "ExternalFlashWrite" : 0, "SongErase" : 0, "SongAppend" : 0, "Stop" : 0, "SendSong" : 0, "SendScene" : 0, "SendShift" : 0,
                       "EnableInitColor" : 0, "TurnToBlack" : 0, "ExternalFlashRead" : 0, "SongRead" : 0, "ComCount" : 0, "StartSong" : 0, "StopSong" : 0}},
               "00-17-0D-00-00-59-60-14" : {"state" : "operational", "ack" : {"SetStartTime" : 0, "EraseExternalFlash" : 0,
                       "ExternalFlashWrite" : 0, "SongErase" : 0, "SongAppend" : 0, "Stop" : 0, "SendSong" : 0, "SendScene" : 0, "SendShift" : 0,
                       "EnableInitColor" : 0, "TurnToBlack" : 0, "ExternalFlashRead" : 0, "SongRead" : 0, "ComCount" : 0, "StartSong" : 0, "StopSong" : 0}},
               "00-17-0D-00-00-59-60-0F" : {"state" : "operational", "ack" : {"SetStartTime" : 0, "EraseExternalFlash" : 0,
                       "ExternalFlashWrite" : 0, "SongErase" : 0, "SongAppend" : 0, "Stop" : 0, "SendSong" : 0, "SendScene" : 0, "SendShift" : 0,
                       "EnableInitColor" : 0, "TurnToBlack" : 0, "ExternalFlashRead" : 0, "SongRead" : 0, "ComCount" : 0, "StartSong" : 0, "StopSong" : 0}},
               "00-17-0D-00-00-59-61-6E" : {"state" : "operational", "ack" : {"SetStartTime" : 0, "EraseExternalFlash" : 0,
                        "ExternalFlashWrite" : 0, "SongErase" : 0, "SongAppend" : 0, "Stop" : 0, "SendSong" : 0, "SendScene" : 0, "SendShift" : 0,
                        "EnableInitColor" : 0, "TurnToBlack" : 0, "ExternalFlashRead" : 0, "SongRead" : 0, "ComCount" : 0, "StartSong" : 0, "StopSong" : 0}},
               "00-17-0D-00-00-60-3E-13" : {"state" : "operational", "ack" : {"SetStartTime" : 0, "EraseExternalFlash" : 0,
                        "ExternalFlashWrite" : 0, "SongErase" : 0, "SongAppend" : 0, "Stop" : 0, "SendSong" : 0, "SendScene" : 0, "SendShift" : 0,
                        "EnableInitColor" : 0, "TurnToBlack" : 0, "ExternalFlashRead" : 0, "SongRead" : 0, "ComCount" : 0, "StartSong" : 0, "StopSong" : 0}},
               "00-17-0D-00-00-60-17-62" : {"state" : "operational", "ack" : {"SetStartTime" : 0, "EraseExternalFlash" : 0,
                        "ExternalFlashWrite" : 0, "SongErase" : 0, "SongAppend" : 0, "Stop" : 0, "SendSong" : 0, "SendScene" : 0, "SendShift" : 0,
                        "EnableInitColor" : 0, "TurnToBlack" : 0, "ExternalFlashRead" : 0, "SongRead" : 0, "ComCount" : 0, "StartSong" : 0, "StopSong" : 0}},
               "00-17-0D-00-00-59-60-27" : {"state" : "operational", "ack" : {"SetStartTime" : 0, "EraseExternalFlash" : 0,
                        "ExternalFlashWrite" : 0, "SongErase" : 0, "SongAppend" : 0, "Stop" : 0, "SendSong" : 0, "SendScene" : 0, "SendShift" : 0,
                        "EnableInitColor" : 0, "TurnToBlack" : 0, "ExternalFlashRead" : 0, "SongRead" : 0, "ComCount" : 0, "StartSong" : 0, "StopSong" : 0}},
               "00-17-0D-00-00-59-56-D3" : {"state" : "operational", "ack" : {"SetStartTime" : 0, "EraseExternalFlash" : 0,
                        "ExternalFlashWrite" : 0, "SongErase" : 0, "SongAppend" : 0, "Stop" : 0, "SendSong" : 0, "SendScene" : 0, "SendShift" : 0,
                        "EnableInitColor" : 0, "TurnToBlack" : 0, "ExternalFlashRead" : 0, "SongRead" : 0, "ComCount" : 0, "StartSong" : 0, "StopSong" : 0}},
               "00-17-0D-00-00-59-63-B3" : {"state" : "operational", "ack" : {"SetStartTime" : 0, "EraseExternalFlash" : 0,
                        "ExternalFlashWrite" : 0, "SongErase" : 0, "SongAppend" : 0, "Stop" : 0, "SendSong" : 0, "SendScene" : 0, "SendShift" : 0,
                        "EnableInitColor" : 0, "TurnToBlack" : 0, "ExternalFlashRead" : 0, "SongRead" : 0, "ComCount" : 0, "StartSong" : 0, "StopSong" : 0}},
               "00-17-0D-00-00-59-65-75" : {"state" : "operational", "ack" : {"SetStartTime" : 0, "EraseExternalFlash" : 0,
                        "ExternalFlashWrite" : 0, "SongErase" : 0, "SongAppend" : 0, "Stop" : 0, "SendSong" : 0, "SendScene" : 0, "SendShift" : 0,
                        "EnableInitColor" : 0, "TurnToBlack" : 0, "ExternalFlashRead" : 0, "SongRead" : 0, "ComCount" : 0, "StartSong" : 0, "StopSong" : 0}},
               "00-17-0D-00-00-59-6D-E0" : {"state" : "operational", "ack" : {"SetStartTime" : 0, "EraseExternalFlash" : 0,
                        "ExternalFlashWrite" : 0, "SongErase" : 0, "SongAppend" : 0, "Stop" : 0, "SendSong" : 0, "SendScene" : 0, "SendShift" : 0,
                        "EnableInitColor" : 0, "TurnToBlack" : 0, "ExternalFlashRead" : 0, "SongRead" : 0, "ComCount" : 0, "StartSong" : 0, "StopSong" : 0}},
               "00-17-0D-00-00-59-5D-B2" : {"state" : "operational", "ack" : {"SetStartTime" : 0, "EraseExternalFlash" : 0,
                        "ExternalFlashWrite" : 0, "SongErase" : 0, "SongAppend" : 0, "Stop" : 0, "SendSong" : 0, "SendScene" : 0, "SendShift" : 0,
                        "EnableInitColor" : 0, "TurnToBlack" : 0, "ExternalFlashRead" : 0, "SongRead" : 0, "ComCount" : 0, "StartSong" : 0, "StopSong" : 0}},
               "00-17-0D-00-00-58-59-1D" : {"state" : "operational", "ack" : {"SetStartTime" : 0, "EraseExternalFlash" : 0,
                        "ExternalFlashWrite" : 0, "SongErase" : 0, "SongAppend" : 0, "Stop" : 0, "SendSong" : 0, "SendScene" : 0, "SendShift" : 0,
                        "EnableInitColor" : 0, "TurnToBlack" : 0, "ExternalFlashRead" : 0, "SongRead" : 0, "ComCount" : 0, "StartSong" : 0, "StopSong" : 0}},

               }
macIDs       = ["00-17-0D-00-00-30-B2-6E" , "00-17-0D-00-00-30-B8-EE" , "00-17-0D-00-00-59-60-14" , "00-17-0D-00-00-59-60-0F" , "00-17-0D-00-00-59-61-6E" ,
                "00-17-0D-00-00-60-3E-13" , "00-17-0D-00-00-60-17-62" , "00-17-0D-00-00-59-60-27" , "00-17-0D-00-00-59-56-D3" , "00-17-0D-00-00-59-63-B3" ,
                "00-17-0D-00-00-59-65-75" , "00-17-0D-00-00-59-6D-E0" , "00-17-0D-00-00-59-5D-B2" , "00-17-0D-00-00-58-59-1D"]

moteSelect   = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
commandCount = 1

macList = []
#============================ End of VManager Specific Header =================

''' Display '''
INIT_X              = 1400
INIT_Y              = 1150

'''     Tube Variables   '''
NUM_TUBES           = 12
NUM_PIXELS          = 30
NUM_COMPS           = 4
ACTIVE_COL          = 7
NUM_COL             = 9
PAL_BUTTON_X        = 25
PAL_BUTTON_Y        = 20
NUM_MOTES           = 14
'''     Tranasition Types  '''''
FADE                = 1
EXP_FADE            = 2
INV_EXP_FADE        = 3
SWIPE_DOWN          = 4
SWIPE_UP            = 5
INIT                = 255
END                 = 254
HOLD                = 253
SHIFT               = 240
TRANS_SEL_OFF       = 1000000
transition_type     = ["FADE", "SW UP", "SW DN", "END", "INIT"]
transition_type_LUT = {"FADE" : 1, "SW UP" : 5, "SW DN" : 4, "END" : 254, "INIT" : 255}
trans_type_rev_LUT  = {1 : "FADE", 5 : "SW UP", 4 : "SW DN", 254 : "END", 255 : "INIT"}
trans_type_len_LUT  = {"FADE" : 8, "SW UP" : 8, "SW DN" : 8, "END" : 4, "INIT" : 4}
redHex              = "00"
greenHex            = "00"
blueHex             = "00"
RED                 = 0
GREEN               = 1
BLUE                = 2
FLICKER             = 3
flicker             = 0
palette_comp_colors = [0, 64, 128, 255]
songNames           = ["song 1", "song 2", "song 3", "song 4", "song 5", "song 6", "song 7", "song 8","song 9", "song 10", "song 11", "song 12"]
songFileNames       = ["song1.wav", "song2.wav", "song3.wav", "song4.wav", "song5.wav", "song6.wav", "song7.wav", "song8.wav", "song9.wav", "song10.wav", "song11.wav", "song12.wav"]
syncFileName        = ["sync_file.wav"]
songLUT             = {}
# Not Used songs               = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]  # FIXME should either be 1 to 12 or 0 to 11
saveSongs           = []
songList            = []
song                = 0
scenes              = []
sceneSpeeds         = []
speedValue          = 0
transitions         = []
tubes               = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]
tube_macs           = ["00-17-0D-00-00-58-59-1D"]
mac_tubenum_LUT     = {"00-17-0D-00-00-58-59-1D" : 0}
tube_bit_field      = 4095
ALL_TUBES           = 4095
transition_stop     = []
trans_stop_LUT      = {}
trans_stop_rev_LUT  = {}
trans_sel_low       = TRANS_SEL_OFF
trans_sel_high      = TRANS_SEL_OFF
currentTransition   = 0
currentScene        = 0
updating            = False
sceneUpdating       = False
moteFileState       = []
selStartTime        = 0
selEndTime          = 0
DECIMAL_POINT       = 4
currTime            = 0
playSequence        = []
play_tube           = []
NUM_FLICKER_SPEEDS  = 16
NUM_FLICKER_SCENES  = 16
FLICKER_OFFSET      = 16384
                     #     0    1   2   3   4   5   6   7   8   9  10  11  12  13 14 15 16
flickerDurations    = [10000, 108, 92, 76, 60, 52, 44, 36, 28, 24, 20, 16, 12, 10, 8, 6, 4]
flickerFilterIndex  = [    0,   3,  3,  3,  3,  2,  2,  2,  2,  1,  1,  1,  1,  0, 0, 0, 0]
flickerFilter       = [[0, 0, 1, 0, 0], [0, 1, 2, 1, 0], [1, 2, 4, 2, 1], [1, 2, 4, 2, 1]]
flickerFilterTotal  = [1, 4, 10, 10]
fickerSceneIndex    = []
flickerScenes       = []

transition = {"type" : "INIT", "stop" : 0, "time" : 0, "duration" : 0, "index" : 0, "tubes" : ALL_TUBES, "relative" : 1, "selection" : 0}

#============================ Audio Specific  =================

CHUNK = 1024  #define stream chunk
is_playing = False
my_thread = None

#============================ VManager Specific Functions =====================

def erase_ext_flash():
    '''
    Erase External Flash of All Motes in the network
    '''
    global commandCount, motes, status_box
    if NETWORK_ON:
        for mote in range(len(macIDs)):
            if status_radio_var[mote].get() == "0":
                motes[macIDs[mote]]["ack"]["EraseExternalFlash"] = 1
            else:
                motes[macIDs[mote]]["ack"]["EraseExternalFlash"] = 0
        allAcksReceived = 0
        dataComCount = struct.pack("i", commandCount)
        commandCount += 1
        msg = struct.pack('!B', PKT_EXTERNAL_FLASH_ERASE)
        msg += dataComCount[0]
        msg_b64 = base64.b64encode(msg)   # Convert from bin to base64
        for i in range(ERASE_TIMEOUT):
            sendapacket(BROADCAST_MOTE_MAC, msg_b64)
            sendapacket(BROADCAST_MOTE_MAC, msg_b64)
            time.sleep(10)
            allAcksReceived = 1
            for mote in motes.keys():
                if motes[mote]["ack"]["EraseExternalFlash"] == 0:
                    allAcksReceived = 0
            if allAcksReceived == 1:
                print ('\n   All External Flashes Erased.\n')
                break
            else:
                allAcksReceived = 0
        for mote in motes.keys():
            if motes[mote]["ack"]["EraseExternalFlash"] == 0:
                print ('\n   External Flashe Not erased in {0}.\n'.format(mote))
        return (allAcksReceived)
    else:
        for mote in range(len(macIDs)):
            motes[macIDs[mote]]["ack"]["EraseExternalFlash"] = 1
        open("scenes.dat", "w").close()
        return (1)


def erase_scenes():
    global moteFileState, status_box

    checkMotes()
    erase_ext_flash()
    for mote in range(len(macIDs)):
        if status_radio_var[mote].get() == "1":
            moteFileState[mote][0] = 0
    display_text = "Erase Scenes Complete"
    display_message(display_text)


def write_external_flash(add, data):
    '''
     Write data to all motes in the network
    '''
    global commandCount, motes

    if NETWORK_ON:
        #macaddr = TEST_MOTE_MAC
        for mote in range(len(macIDs)):
            if status_radio_var[mote].get() == "0":
                motes[macIDs[mote]]["ack"]["ExternalFlashWrite"] = 1
            else:
                motes[macIDs[mote]]["ack"]["ExternalFlashWrite"] = 0
        allAcksReceived = 0
        dataComCount = struct.pack("i", commandCount)
        commandCount += 1
        addString = struct.pack("i", add)
        dataLength = struct.pack("i", len(data))
        dataString = ''.join(chr(e) for e in data)
        msg = struct.pack('!B', PKT_EXTERNAL_FLASH_WRITE)
        msg += dataComCount[0] + addString + dataLength[0] + dataString
        msg_b64 = base64.b64encode(msg)   # Convert from bin to base64
        for i in range(WRITE_TIMEOUT):
            sendapacket(BROADCAST_MOTE_MAC, msg_b64)
            time.sleep(PKT_REPEAT_DELAY)
            allAcksReceived = 1
            for mote in motes.keys():
                if motes[mote]["ack"]["ExternalFlashWrite"] == 0:
                    allAcksReceived = 0
            if allAcksReceived == 1:
                break
        if (allAcksReceived == 1):
            print '\n   Address "{0}" Written \n'.format(add)
        else:
            print '\n***   Address "{0}" Not Written - not all acks received \n'.format(add)
        return (allAcksReceived)
    else:
        for mote in range(len(macIDs)):
            motes[macIDs[mote]]["ack"]["ExternalFlashWrite"] = 1
        with open("scenes.dat", "a") as textfile:
            for i in range(len(data)):
                dataString = str(data[i]).zfill(3)
                addString = str(add+i).zfill(7)
                writeString = addString + " " + dataString + "\n"
                textfile.write(writeString)
        return (1)



def send_scene(localmac, add):
    '''
    Request the motes to send a particular scene in external flash
    '''
    global commandCount, motes
    try:
        for mote in range(len(macIDs)):
            motes[macIDs[mote]]["ack"]["SendScene"] = 1
        if (localmac == BROADCAST_MOTE_MAC):
            for mote in range(len(macIDs)):
                if status_radio_var[mote].get() == "1":
                    motes[macIDs[mote]]["ack"]["SendScene"] = 0
        else:
            motes[localmac]["ack"]["SendScene"] = 0
        allAcksReceived = 0
        dataComCount = struct.pack("i", commandCount)
        commandCount += 1
        addString = struct.pack("i", add)
        msg = struct.pack('!B', PKT_SEND_SCENE)
        msg += dataComCount[0] + addString
        msg_b64 = base64.b64encode(msg)   # Convert from bin to base64
        for i in range(ERASE_TIMEOUT):
            sendapacket(localmac, msg_b64)
            time.sleep(PKT_REPEAT_DELAY)
            allAcksReceived = 1
            for mote in motes.keys():
                if motes[mote]["ack"]["SendScene"] == 0:
                    allAcksReceived = 0
            if allAcksReceived == 1:
                break
        return (allAcksReceived)
    except:
        print ('\n   ERROR -- Could not Execute Command\n')
    else:
        print ('\n   All Scenes Received.\n')


def list_files(localmac, add):
    '''
    Request the motes to send a particular scene in external flash
    '''
    global commandCount, motes
    try:
        for mote in range(len(macIDs)):
            motes[macIDs[mote]]["ack"]["SendScene"] = 1
        if (localmac == BROADCAST_MOTE_MAC):
            for mote in range(len(macIDs)):
                if status_radio_var[mote].get() == "1":
                    motes[macIDs[mote]]["ack"]["SendScene"] = 0
        else:
            motes[localmac]["ack"]["SendScene"] = 0
        allAcksReceived = 0
        dataComCount = struct.pack("i", commandCount)
        commandCount += 1
        addString = struct.pack("i", add)
        msg = struct.pack('!B', PKT_SEND_SCENE)
        msg += dataComCount[0] + addString
        msg_b64 = base64.b64encode(msg)   # Convert from bin to base64
        for x in range(NUM_WRITE_RETRIES):
            sendapacket(localmac, msg_b64)
            time.sleep(PKT_REPEAT_DELAY)
        for i in range(ERASE_TIMEOUT):
            allAcksReceived = 1
            for mote in motes.keys():
                if motes[mote]["ack"]["SendScene"] == 0:
                    allAcksReceived = 0
            if allAcksReceived == 1:
                break
            time.sleep(1)
        return (allAcksReceived)
    except:
        print ('\n   ERROR -- Could not Execute Command\n')
    else:
        print ('\n   All Scenes Received.\n')


def song_erase(localmac, song):
    '''
    Erase Song in all Motes in the network
    '''
    global commandCount, motes

    if NETWORK_ON:
        for mote in range(len(macIDs)):
            motes[macIDs[mote]]["ack"]["SongErase"] = 1
        if (localmac == BROADCAST_MOTE_MAC):
            for mote in range(len(macIDs)):
                if status_radio_var[mote].get() == "1":
                    motes[macIDs[mote]]["ack"]["SongErase"] = 0
        else:
            motes[localmac]["ack"]["SongErase"] = 0
        allAcksReceived = 0
        dataComCount = struct.pack("i", commandCount)
        commandCount += 1
        songString = struct.pack("i", song)
        msg = struct.pack('!B', PKT_SONG_ERASE)
        msg += dataComCount[0] + songString[0]
        msg_b64 = base64.b64encode(msg)   # Convert from bin to base64
        for i in range(ERASE_TIMEOUT):
            sendapacket(localmac, msg_b64)
            time.sleep(PKT_REPEAT_DELAY)
            allAcksReceived = 1
            for mote in motes.keys():
                if motes[mote]["ack"]["SongErase"] == 0:
                    allAcksReceived = 0
            if allAcksReceived == 1:
                break
        if (allAcksReceived == 1):
            print '\n   Song "{0}" Erased\n'.format(song)
        else:
            print '\n***  Song "{0}" not erased - not all acks received \n'.format(song)
        return (allAcksReceived)
    else:
        for mote in range(len(macIDs)):
            motes[macIDs[mote]]["ack"]["SongErase"] = 1
        songFileName = "Mote" + str(macIDs.index(localmac)) + "_song" + str(song) + ".dat"
        open(songFileName, "w").close()
        return (1)

def append_song(localmac, song, data):
    '''
     Write data to all motes in the network
    '''
    global commandCount, motes

    if NETWORK_ON:
        for mote in range(len(macIDs)):
            motes[macIDs[mote]]["ack"]["SongAppend"] = 1
        if (localmac == BROADCAST_MOTE_MAC):
            for mote in range(len(macIDs)):
                if status_radio_var[mote].get() == "1":
                    motes[macIDs[mote]]["ack"]["SongAppend"] = 0
        else:
            motes[localmac]["ack"]["SongAppend"] = 0
        allAcksReceived = 0
        if (len(data) <= MAX_SONG_APPEND_LEN):
            dataComCount = struct.pack("i", commandCount)
            commandCount += 1
            songString = struct.pack("i", song)
            dataLength = struct.pack("i", len(data))
            dataString = ''.join(chr(e) for e in data)
            msg = struct.pack('!B', PKT_SONG_APPEND)
            msg += dataComCount[0] + songString[0] + dataLength[0] + dataString
            msg_b64 = base64.b64encode(msg)   # Convert from bin to base64
            for i in range(WRITE_TIMEOUT):
                sendapacket(localmac, msg_b64)
                time.sleep(PKT_REPEAT_DELAY)
                allAcksReceived = 1
                for mote in motes.keys():
                    if motes[mote]["ack"]["SongAppend"] == 0:
                        allAcksReceived = 0
                if allAcksReceived == 1:
                    break
            if (allAcksReceived == 1):
                print '\n   Appended data to Song "{0}"\n'.format(song)
            else:
                print '\n***  Data not appended to Song "{0}" - not all acks received \n'.format(song)
            return (allAcksReceived)
        else:
            print ('\n   ERROR -- data too long for packet\n')
            return (RC_DATA_TOO_LONG)
    else:
        for mote in range(len(macIDs)):
            motes[macIDs[mote]]["ack"]["SongAppend"] = 1
        songFileName = "Mote" + str(macIDs.index(localmac)) + "_song" + str(song) + ".dat"
        with open(songFileName, "a") as textfile:
            for i in range(len(data)):
                dataString = str(data[i]).zfill(3) + "\n"
                textfile.write(dataString)
        return (1)


def reset_com_count(localmac):
    global commandCount, motes

    if NETWORK_ON:
        print ('\n  Executing Command Count\n')
        for mote in range(len(macIDs)):
            motes[macIDs[mote]]["ack"]["ComCount"] = 0
        allAcksReceived = 0
        commandCount = 2
        msg = struct.pack('!BB', PKT_RESET_COM_COUNT, 0x01)
        msg_b64 = base64.b64encode(msg)   # Convert from bin to base64
        for x in range(NUM_ERASE_RETRIES):
            sendapacket(BROADCAST_MOTE_MAC, msg_b64)
        for i in range(RESET_COM_COUNT_TIMEOUT):
            allAcksReceived = 1
            for mote in motes.keys():
                if motes[mote]["ack"]["ComCount"] == 0:
                    allAcksReceived = 0
            if allAcksReceived == 1:
                break
            time.sleep(0.25)
        if (allAcksReceived == 1):
            print '\n   Reset Com Count Complete\n'
        else:
            print '\n***  Reset Com Count Failed - not all acks received \n'
        return (allAcksReceived)
    else:
        for mote in range(len(macIDs)):
            motes[macIDs[mote]]["ack"]["ComCount"] = 1

def stopSong():
    global commandCount, motes, stream, is_playing

    global is_playing

    if is_playing:
        is_playing = False
        my_thread.join()
    if NETWORK_ON:
        for mote in range(len(macIDs)):
            if status_radio_var[mote].get() == "1":
                motes[macIDs[mote]]["ack"]["StopSong"] = 0
            else:
                motes[macIDs[mote]]["ack"]["StopSong"] = 1
        dataComCount = struct.pack("i", commandCount)
        commandCount += 1
        allAcksReceived = 0
        msg = struct.pack('!B', PKT_STOP)
        msg += dataComCount[0]
        msg_b64 = base64.b64encode(msg)   # Convert from bin to base64
        for i in range(STOP_TIMEOUT):
            sendapacket(BROADCAST_MOTE_MAC, msg_b64)
            time.sleep(PKT_REPEAT_DELAY)
            allAcksReceived = 1
            for mote in motes.keys():
                if motes[mote]["ack"]["StopSong"] == 0:
                    allAcksReceived = 0
            if allAcksReceived == 1:
                break
        return (allAcksReceived)


def send_start_of_song(song, offset, chirpTimeS, chirpTimeuS):
    '''
    Send start of song time
    '''
    global commandCount, motes, radio_staus
    if NETWORK_ON:
        for mote in range(len(macIDs)):
            if radio_status[mote] == 0 :
                motes[macIDs[mote]]["ack"]["SetStartTime"] = 1
            else:
                motes[macIDs[mote]]["ack"]["SetStartTime"] = 0
        dataComCount = struct.pack("i", commandCount)
        commandCount += 1
        chirpTimeuS += SOS_DELAY_US
        if chirpTimeuS > 1000000:
            chirpTimeuS -= 1000000
            chirpTimeS += 1 + SOS_DELAY_S
        else:
            chirpTimeS += SOS_DELAY_S
        offsetString      = struct.pack("I", offset)
        chirpTimeSstring  = struct.pack("I", chirpTimeS)
        chirpTimeuSstring = struct.pack("I", chirpTimeuS)
        dataSong          = struct.pack("i", song)
        print 'Starting song[{0}] {1} S, {2} uS'.format(song, chirpTimeS, chirpTimeuS)
        msg = struct.pack('!B', PKT_SET_START_TIME)
        msg += dataComCount[0] + dataSong[0] + offsetString + chirpTimeSstring + chirpTimeuSstring
        msg_b64 = base64.b64encode(msg)   # Convert from bin to base64
        for i in range(SEND_SONG_TIMEOUT):
            sendapacket(BROADCAST_MOTE_MAC, msg_b64)
            time.sleep(0.25)
            allAcksReceived = 1
            for mote in motes.keys():
                if motes[mote]["ack"]["SetStartTime"] == 0:
                    allAcksReceived = 0
            if allAcksReceived == 1:
                break
        if allAcksReceived == 0:
            print ('\n   ERROR -- Could not Execute Start of Song Command\n')
        else:
            print '\n   Start of Song Executed for Song {0}.\n'.format(song+1)
        return (allAcksReceived)

def send_song(localmac, song):
    '''
    Request the motes to send a particular song in internal flash
    '''
    global commandCount, motes
    try:
        for mote in range(len(macIDs)):
            if status_radio_var[mote].get() == "0":
                motes[macIDs[mote]]["ack"]["SendSong"] = 1
            else:
                motes[macIDs[mote]]["ack"]["SendSong"] = 0
        allAcksReceived = 0
        dataComCount = struct.pack("i", commandCount)
        dataSong     = struct.pack("i", song)
        commandCount += 1
        msg = struct.pack('!B', PKT_SEND_SONG)
        msg += dataComCount[0] + dataSong[0]
        print ('\n   Working.\n')
        msg_b64 = base64.b64encode(msg)   # Convert from bin to base64
        for i in range(ERASE_TIMEOUT):
            sendapacket(localmac, msg_b64)
            time.sleep(PKT_REPEAT_DELAY)
            allAcksReceived = 1
            for mote in motes.keys():
                if motes[mote]["ack"]["SendSong"] == 0:
                    allAcksReceived = 0
            if allAcksReceived == 1:
                break
        if not allAcksReceived == 1:
            display_text = "*** WARNING song start %d was not recevied by all motes" % (song)
            display_message(display_text);
            for mote in range(len(macIDs)):
                if status_radio_var[mote].get() == "1":
                    if motes[macIDs[mote]]["ack"]["SendSong"] == 0:
                        print macIDs[mote], " did not receive start of song ", song
        return (allAcksReceived)
    except:
        print ('\n   ERROR -- Could not Execute Command\n')
    else:
        print ('\n   All Songs Received.\n')


def sendapacket(mymac, mydata):

    #Send data to all motes via broadcast.

    try:
        myPayload = DataPacketSendInfo()
        myPayload.src_port   = LED_APP_PORT
        myPayload.dest_port  = LED_APP_PORT
        myPayload.priority   = PRIORITY
        myPayload.payload    = mydata
        # send the data packet
        voyager.motesApi.send_data_packet(mymac, myPayload)
    except:
        print ('\n   ERROR -- Could not send data.\n')
    else:
        intdata = [ ord(c) for c in codecs.decode(mydata, 'base64') ]
        print '\n   Sending packet: "{0}" to {1} \n'.format(intdata, mymac)


def process_data(mydata):

    global song, musicStartTime
    '''
    Processes received data. Prints MAC address of source and packet content.
    '''
    localmacaddr = mydata.mac_address
    # The following was used in the example but returns a string of nibble values - Want to work with bytes so use codecs.decode instead.
    datapayload = (base64.b64decode(mydata.payload)).encode('hex')
    stringpayload = codecs.decode(mydata.payload, 'base64')
    intpayload = [ ord(c) for c in stringpayload ]
    print ' Alt Int  Payload 1 from mote {0} --> {1}'.format(localmacaddr, intpayload)
    if intpayload[0] == PKT_EXTERNAL_FLASH_ERASE:
        if intpayload[1] == LED_ACK:
            print ' EXT FLASH ERASE ACK from mote {0} --> {1}'.format(localmacaddr, datapayload)
            motes[localmacaddr]["ack"]["EraseExternalFlash"] = 1
        else:
            print ' NAK from mote {0} --> {1}'.format(localmacaddr, datapayload)
    elif intpayload[0] == PKT_SET_START_TIME:
        if intpayload[1] == LED_ACK:
            print ' START TIME ACK from mote {0} --> {1}'.format(localmacaddr, datapayload)
            motes[localmacaddr]["ack"]["SetStartTime"] = 1
        else:
            print ' NAK from mote {0} --> {1}'.format(localmacaddr, datapayload)
    elif intpayload[0] == PKT_EXTERNAL_FLASH_WRITE:
        if intpayload[1] == LED_ACK:
            print ' EXT FLASH WRITE ACK from mote {0} --> {1}'.format(localmacaddr, datapayload)
            motes[localmacaddr]["ack"]["ExternalFlashWrite"] = 1
        else:
            print ' EXT FLASH WRITE NAK from mote {0} --> {1}'.format(localmacaddr, datapayload)
    elif intpayload[0] == PKT_SONG_ERASE:
        if intpayload[1] == LED_ACK:
            print ' SONG ERASE ACK from mote {0} --> {1}'.format(localmacaddr, datapayload)
            motes[localmacaddr]["ack"]["SongErase"] = 1
        else:
            print ' SONG ERASE NAK from mote {0} --> {1}'.format(localmacaddr, datapayload)
    elif intpayload[0] == PKT_SONG_APPEND:
        if intpayload[1] == LED_ACK:
            print ' SONG APPEND ACK from mote {0} --> {1}'.format(localmacaddr, datapayload)
            motes[localmacaddr]["ack"]["SongAppend"] = 1
        else:
            print ' SONG APPEND NAK from mote {0} --> {1}'.format(localmacaddr, datapayload)
    elif intpayload[0] == PKT_SEND_SCENE:
        if intpayload[1] == LED_ACK:
            print ' SEND_SCENE ACK from mote {0} --> {1}'.format(localmacaddr, datapayload)
            motes[localmacaddr]["ack"]["SendScene"] = 1
        else:
            print ' SEND SCENE NAK from mote {0} --> {1}'.format(localmacaddr, datapayload)
    elif intpayload[0] == PKT_SEND_SHIFT:
        if intpayload[1] == LED_ACK:
            print ' SEND SHIFT ACK from mote {0} --> {1}'.format(localmacaddr, datapayload)
            motes[localmacaddr]["ack"]["SendShift"] = 1
        else:
            print ' SEND SHIFT NAK from mote {0} --> {1}'.format(localmacaddr, datapayload)
    elif intpayload[0] == PKT_ENABLE_INIT_COLOR:
        if intpayload[1] == LED_ACK:
            print ' ENABLE INIT COLOR ACK from mote {0} --> {1}'.format(localmacaddr, datapayload)
            motes[localmacaddr]["ack"]["EnableInitColor"] = 1
        else:
            print ' ENABLE INIT COLOR NAK from mote {0} --> {1}'.format(localmacaddr, datapayload)
    elif intpayload[0] == PKT_TURN_TO_BLACK:
        if intpayload[1] == LED_ACK:
            print ' TURN TO BLACK ACK from mote {0} --> {1}'.format(localmacaddr, datapayload)
            motes[localmacaddr]["ack"]["TurnToBlack"] = 1
        else:
            print ' TURN TO BLACK NAK from mote {0} --> {1}'.format(localmacaddr, datapayload)
    elif intpayload[0] == PKT_EXTERNAL_FLASH_READ:
        if intpayload[1] == LED_ACK:
            print ' EXT FLASH READ ACK from mote {0} --> {1}'.format(localmacaddr, datapayload)
            motes[localmacaddr]["ack"]["ExternalFlashRead"] = 1
        else:
            print ' EXT FLASH READ NAK from mote {0} --> {1}'.format(localmacaddr, datapayload)
    elif intpayload[0] == PKT_SONG_READ:
        if intpayload[1] == LED_ACK:
            print ' SONG READ ACK from mote {0} --> {1}'.format(localmacaddr, datapayload)
            motes[localmacaddr]["ack"]["SongRead"] = 1
            readFragment = struct.unpack('!H', stringpayload[2:3])
            lastFragment = intpayload[4]
            print 'Fragment = {0}, Last Fragment = {1}'.format(readFragment, lastFragment)
        else:
            print ' SONG READ NAK from mote {0} --> {1}'.format(localmacaddr, datapayload)
    elif intpayload[0] == PKT_RESET_COM_COUNT:
        if intpayload[1] == LED_ACK:
            print ' RESET COM COUNT ACK from mote {0} --> {1}'.format(localmacaddr, datapayload)
            motes[localmacaddr]["ack"]["ComCount"] = 1
        else:
            print ' RESET COM COUNT NAK from mote {0} --> {1}'.format(localmacaddr, datapayload)
    elif intpayload[0] == PKT_SEND_SONG:
        if intpayload[1] == LED_ACK:
            print ' SEND SONG ACK from mote {0} --> {1}'.format(localmacaddr, datapayload)
            motes[localmacaddr]["ack"]["SendSong"] = 1
        else:
            print ' RESET COM COUNT NAK from mote {0} --> {1}'.format(localmacaddr, datapayload)
    elif intpayload[0] == PKT_REPORT_TIME:
        chirpTimeS  = struct.unpack('!I', stringpayload[1:5])
        chirpTimeuS = struct.unpack('!I', stringpayload[5:9])
        startOfSongPCTime = int(round(time.time()))
        print 'Chirp Time from mote {0} S, {1} uS at PCTime {2}'.format(chirpTimeS[0], chirpTimeuS[0], startOfSongPCTime)
        send_start_of_song(song, musicStartTime, chirpTimeS[0], chirpTimeuS[0])
        currTime = int(round(time.time()))
        songDeltaTime = currTime - startOfSongPCTime
        print "After Starting Song : {0} , Delta Time {1}".format(currTime, songDeltaTime)
        n = 1
    else:
        print ' Data from mote {0} --> {1}'.format(localmacaddr, datapayload)
        print ' Source Port from mote {0}'.format(mydata.src_port)
        print ' Dest Port from mote {0}'.format(mydata.dest_port)
        print ' Latency from mote {0}'.format(mydata.latency)
        print ' Hops from mote {0}'.format(mydata.hops)
        print ' gen_net_time from mote {0}'.format(mydata.gen_net_time)

#============================ End of VManager Specific Functions =====================

def downloadScenes():
    global moteFileState

    checkMotes()
    for mote in range(len(macIDs)):
        if status_radio_var[mote].get() == "1" and moteFileState[mote][0] < 1:  #Only erase external flash if the current write state indicates
            erase_ext_flash()
            blah = 1
    min_index = len(scenes)
    for mote in range(len(macIDs)):
        if status_radio_var[mote].get() == "1":
            if moteFileState[mote][0] < min_index:
                min_index = moteFileState[mote][0]

    print "Min index : ", min_index, "num of scenes : ", len(scenes)

    for index in range(min_index, len(scenes)):
        print "*** Writing scene index :", index
        add = index * 128 + 4
        print "Adddress : ", add
        data = []
        for pixel in range(NUM_PIXELS-1, NUM_PIXELS/2-1, -1):   # Reverse Pixel order so 1 is at the top of the tube
            gainedFlicker = int(scenes[index][pixel][FLICKER] * 255 / 100)
            data.append(gainedFlicker)
            for comp in [RED, GREEN, BLUE]:   #manually order data - definitions not consistent
                data.append(scenes[index][pixel][comp])
        print "1st Half : ", data
        write_external_flash(add, data)
        add = index * 128 + 64
        print "Adddress : ", add
        data = []
        for pixel in range(NUM_PIXELS/2-1, -1, -1):
            gainedFlicker = int(scenes[index][pixel][FLICKER] * 255 / 100)
            data.append(gainedFlicker)
            for comp in [RED, GREEN, BLUE]:   #manually order data - definitions not consistent
                data.append(scenes[index][pixel][comp])
        print "2nd Half : ", data
        write_external_flash(add, data)

    for mote in range(len(macIDs)):
        if status_radio_var[mote].get() == "1":
            moteFileState[mote][0] = len(scenes)
    display_text = "Download Scenes Complete"
    display_message(display_text)


def downloadSongs():

    checkMotes()
    for mote in range(len(macIDs)):
        if status_radio_var[mote].get() == "1" and not mote_assign[mote].get() == "0":
            tubeBit = tubes[int(mote_assign[mote].get())-1]
            for song_index in range(len(songNames)):
                print "Song [", song_index, "]"
                data = []
                transList = []
                packetCount = 0
                songSize = 0
                for t_index in range(len(transitions[song_index])):
                    if (transitions[song_index][t_index]["tubes"] & tubeBit) > 0:
                        transList.append(t_index)
                if len(transList) > 2:  # Don't slow down writing empty song
                    song_erase(macIDs[mote], song_index)
                    data.append(transition_type_LUT["INIT"])
                    data.append(0)
                    data.extend([transitions[song_index][transList[0]]["index"] >> i & 0xff for i in (0,8)])
                    length = 4
                    #if the start time of the first transition after init > 0 insert a transition with the same index as the INIT and the corresponding hold time
                    if transitions[song_index][transList[1]]["time"] > 0:
                        data.append(transition_type_LUT["FADE"])
                        data.append(0)
                        data.extend([transitions[song_index][transList[0]]["index"] >> i & 0xff for i in (0,8)])  # Use index from INIT
                        data.extend([0, 0]) # length transtion
                        data.extend([transitions[song_index][transList[1]]["time"] >> i & 0xff for i in (0,8)])  # Back Porch = duration to first transtion
                        length = 12
                    for t_index in range(1, len(transList)):
                        if length + trans_type_len_LUT[transitions[song_index][transList[t_index]]["type"]] > 74:
                            packetCount += 1
                            songSize += len(data)
                            append_song(macIDs[mote], song_index, data)
                            print "Mote [", mote, "], Song [", song, "] Current Index : ", transList[t_index], " Packet :",packetCount, " Song Size : ", songSize, "  Song Packet : ", data
                            data = []
                            length = 0
                        data.append(transition_type_LUT[transitions[song_index][transList[t_index]]["type"]])
                        data.append(transitions[song_index][transList[t_index]]["stop"])
                        length += 2
                        if transitions[song_index][transList[t_index]]["type"] in ["FADE", "SW UP", "SW DN"]:
                            data.extend([transitions[song_index][transList[t_index]]["index"] >> i & 0xff for i in (0,8)])
                            if transitions[song_index][transList[t_index]]["duration"] < 1:  # rounding error on scaling can generate negative / zero values
                                transitions[song_index][transList[t_index]]["duration"] = 1
                            data.extend([transitions[song_index][transList[t_index]]["duration"] >> i & 0xff for i in (0,8)])  # Use index from INIT
                            back_porch = transitions[song_index][transList[t_index+1]]["time"]-transitions[song_index][transList[t_index]]["time"]-transitions[song_index][transList[t_index]]["duration"]
                            if back_porch < 0:   # rounding error on scaling can generate negative values
                                back_porch = 0
                            data.extend([back_porch >> i & 0xff for i in (0,8)])  # Back Porch = duration to first transtion
                            length += 6
                        elif transitions[song_index][transList[t_index]]["type"] in ["END"]:
                            data.extend([0, 0])
                            length += 2
                            append_song(macIDs[mote], song_index, data)
                            break
    display_text = "Download Songs Complete"
    display_message(display_text)

def isFlicker(index):
    global scenes

    for pixel in range(NUM_PIXELS):
        if scenes[index][pixel][FLICKER] > 0:
            return True
    return False

def flickerScene(baseScene):
    global scenes, sceneSpeeds

    flickerStart = []
    flickerFinal = []
    finalScene = []
    flickerSpeed = sceneSpeeds[baseScene]
    filterIndex = flickerFilterIndex[flickerSpeed]
    for pixel in range(NUM_PIXELS):
        randVal = randint(0, scenes[baseScene][pixel][FLICKER]*255/100)
        randSquare = 255 - int((randVal * randVal) / 255)
        flickerStart.append(randSquare)
    for pixel in range(NUM_PIXELS):
        pixelList = []
        cumTotal = 0
        cumFlicker = 0
        if flickerStart[pixel] == 0:
            cumFlicker = 0
            cumTotal   = 1
        else:
            cumTotal = flickerFilter[filterIndex][2]
            cumFlicker += flickerStart[pixel] * flickerFilter[filterIndex][2]
            if (pixel - 1) > 0 and flickerStart[pixel - 1] > 0:
                cumFlicker += flickerStart[pixel-1] * flickerFilter[filterIndex][1]
                cumTotal += flickerFilter[filterIndex][1]
                if (pixel - 2) > 0 and flickerStart[pixel - 2] > 0:
                    cumFlicker += flickerStart[pixel-2] * flickerFilter[filterIndex][0]
                    cumTotal += flickerFilter[filterIndex][0]
            if (pixel + 1) < 30 and flickerStart[pixel + 1] > 0:
                cumFlicker += flickerStart[pixel-1] * flickerFilter[filterIndex][3]
                cumTotal += flickerFilter[filterIndex][3]
                if (pixel + 2) < 30 and flickerStart[pixel + 2] > 0:
                    cumFlicker += flickerStart[pixel+2] * flickerFilter[filterIndex][4]
                    cumTotal += flickerFilter[filterIndex][4]
        flickerFinal.append(int(cumFlicker/cumTotal))
        pixelList.append(int((scenes[baseScene][pixel][RED]   * (255 - flickerFinal[pixel]))/255))
        pixelList.append(int((scenes[baseScene][pixel][GREEN] * (255 - flickerFinal[pixel]))/255))
        pixelList.append(int((scenes[baseScene][pixel][BLUE]  * (255 - flickerFinal[pixel]))/255))
        pixelList.append(0)
        finalScene.append(list(pixelList))
    return finalScene

def createFlickerScenes():
    global flickerScenes, scenes, flickerSceneIndex

    flickerScenes = []
    flickerSceneIndex = []
    baseIndex = 16384
    for index in range(len(scenes)):
        if isFlicker(index):
            print "*** Writing flicker for index :", index
            for f_index in range(NUM_FLICKER_SCENES):
                flickerScenes.append(flickerScene(index))
                add = (baseIndex + f_index) * 128 + 4
                print "Adddress : ", add
                data = []
                for pixel in range(NUM_PIXELS-1, NUM_PIXELS/2-1, -1):   # Reverse Pixel order so 1 is at the top of the tube
                    data.append(0) # no flicker
                    for comp in [RED, GREEN, BLUE]:   #manually order data - definitions not consistent
                        data.append(flickerScenes[f_index][pixel][comp])
                print "1st Half : ", data
                write_external_flash(add, data)
                add = (baseIndex + f_index) * 128 + 64
                print "Adddress : ", add
                data = []
                for pixel in range(NUM_PIXELS/2-1, -1, -1):
                    data.append(0) # no flicker
                    for comp in [RED, GREEN, BLUE]:   #manually order data - definitions not consistent
                        data.append(flickerScenes[f_index][pixel][comp])
                print "2nd Half : ", data
                write_external_flash(add, data)
            flickerSceneIndex.append(baseIndex)
            baseIndex += 16
        else:
            flickerSceneIndex.append(0)

def downloadFull():

    checkMotes()
    downloadScenes()
    createFlickerScenes()
    downloadOneSong(0)
    downloadOneSong(1)

def downloadOneSong(song_index):

    numScenes = len(scenes)
    for mote in range(len(macIDs)):
        if status_radio_var[mote].get() == "1" and not mote_assign[mote].get() == "0":
            tubeBit = tubes[int(mote_assign[mote].get())-1]
            print "Song [", song_index, "]"
            data = []
            transList = []
            flickerScenes = []
            packetCount = 0
            songSize = 0
            for t_index in range(len(transitions[song_index])):
                if (transitions[song_index][t_index]["tubes"] & tubeBit) > 0:
                    transList.append(t_index)
            # First is always an INIT
            if len(transList) > 2:  # Don't slow down writing empty song
                song_erase(macIDs[mote], song_index)
                data.append(transition_type_LUT["INIT"])
                data.append(0)
                data.extend([transitions[song_index][transList[0]]["index"] >> i & 0xff for i in (0,8)])
                length = 4
                if transitions[song_index][transList[1]]["time"] > 0:
                    if isFlicker(transitions[song_index][transList[0]]["index"]):
                        flickerSpeed  = sceneSpeeds[transitions[song_index][transList[1]]["index"]]
                        remainingTime = transitions[song_index][transList[1]]["time"]
                        indexOffset = randint(0, NUM_FLICKER_SCENES)
                        while (remainingTime > 0):
                            if remainingTime < flickerDurations[flickerSpeed]:
                                transTime     = remainingTime
                                remainingTime = 0
                            else:
                                transTime      = flickerDurations[flickerSpeed]
                                remainingTime -= transTime
                            data.append(transition_type_LUT["FADE"])
                            data.append(0)
                            data.extend([(flickerSceneIndex[transitions[song_index][transList[1]]["index"]] + indexOffset) >> i & 0xff for i in (0,8)])
                            data.extend([transTime >> i & 0xff for i in (0,8)])  # Transition time set to lesser of remaining time or flicker duration
                            data.extend([0, 0]) # Back Porch of Zero
                            nextIndexOffset = randint(0, NUM_FLICKER_SCENES)
                            while (nextIndexOffset == indexOffset):
                                nextIndexOffset = randint(0, NUM_FLICKER_SCENES)
                            indexOffset = nextIndexOffset
                            length += 8
                            if (length + 8) > 74:
                                packetCount += 1
                                songSize += len(data)
                                append_song(macIDs[mote], song_index, data)
                                print "Mote [", mote, "], Song [", song, "] Current Index : ", transList[t_index], " Packet :",packetCount, " Song Size : ", songSize, "  Song Packet : ", data
                                data = []
                                length = 0
                    else:
                        data.append(transition_type_LUT["FADE"])
                        data.append(0)
                        data.extend([transitions[song_index][transList[0]]["index"] >> i & 0xff for i in (0,8)])  # Use index from INIT
                        data.extend([0, 0]) # length transtion
                        data.extend([transitions[song_index][transList[1]]["time"] >> i & 0xff for i in (0,8)])  # Back Porch = duration to first transtion
                        length = 12
                for t_index in range(1, len(transList)):
                    if length + trans_type_len_LUT[transitions[song_index][transList[t_index]]["type"]] > 74:
                        packetCount += 1
                        songSize += len(data)
                        append_song(macIDs[mote], song_index, data)
                        print "Mote [", mote, "], Song [", song, "] Current Index : ", transList[t_index], " Packet :",packetCount, " Song Size : ", songSize, "  Song Packet : ", data
                        data = []
                        length = 0
                    if transitions[song_index][transList[t_index]]["type"] in ["END"]:
                        data.append(transition_type_LUT[transitions[song_index][transList[t_index]]["type"]])
                        data.append(transitions[song_index][transList[t_index]]["stop"])
                        data.extend([0, 0])
                        length += 4
                        append_song(macIDs[mote], song_index, data)
                        break
                    flickerSpeed  = sceneSpeeds[transitions[song_index][transList[t_index]]["index"]]
                    back_porch    = transitions[song_index][transList[t_index+1]]["time"]-transitions[song_index][transList[t_index]]["time"]-transitions[song_index][transList[t_index]]["duration"]
                    currIndex     = transitions[song_index][transList[t_index]]["index"]
                    if isFlicker(currIndex) and back_porch > flickerDurations[sceneSpeeds[currIndex]]:
                        # Add transition with back porch of zero
                        data.append(transition_type_LUT[transitions[song_index][transList[t_index]]["type"]])
                        data.append(transitions[song_index][transList[t_index]]["stop"])
                        indexOffset = randint(0, NUM_FLICKER_SCENES)
                        data.extend([(flickerSceneIndex[currIndex] + indexOffset) >> i & 0xff for i in (0,8)])
                        if transitions[song_index][transList[t_index]]["duration"] < 1:  # rounding error on scaling can generate negative / zero values
                            transitions[song_index][transList[t_index]]["duration"] = 1
                        data.extend([transitions[song_index][transList[t_index]]["duration"] >> i & 0xff for i in (0,8)])
                        data.extend([0, 0]) # Back Porch of Zero
                        length += 8
                        if (length + 8) > 74:
                            packetCount += 1
                            songSize += len(data)
                            append_song(macIDs[mote], song_index, data)
                            print "Mote [", mote, "], Song [", song, "] Current Index : ", transList[t_index], " Packet :",packetCount, " Song Size : ", songSize, "  Song Packet : ", data
                            data = []
                            length = 0
                        # Add series of transitions for flicker where back porch used to be, set flicker for all of these to zero
                        remainingTime = back_porch
                        while (remainingTime > 0):
                            if remainingTime < flickerDurations[flickerSpeed]:
                                transTime     = remainingTime
                                remainingTime = 0
                            else:
                                transTime      = flickerDurations[flickerSpeed]
                                remainingTime -= transTime
                            data.append(transition_type_LUT["FADE"])
                            data.append(0)
                            nextIndexOffset = randint(0, NUM_FLICKER_SCENES)
                            while (nextIndexOffset == indexOffset):
                                nextIndexOffset = randint(0, NUM_FLICKER_SCENES)
                            indexOffset = nextIndexOffset
                            data.extend([(flickerSceneIndex[currIndex] + indexOffset) >> i & 0xff for i in (0,8)])
                            data.extend([transTime >> i & 0xff for i in (0,8)])  # Transition time set to lesser of remaining time or flicker duration
                            data.extend([0, 0]) # Back Porch of Zero
                            length += 8
                            if (length + 8) > 74:
                                packetCount += 1
                                songSize += len(data)
                                append_song(macIDs[mote], song_index, data)
                                print "Mote [", mote, "], Song [", song, "] Current Index : ", transList[t_index], " Packet :",packetCount, " Song Size : ", songSize, "  Song Packet : ", data
                                data = []
                                length = 0
                    elif transitions[song_index][transList[t_index]]["type"] in ["FADE", "SW UP", "SW DN"]:
                        data.append(transition_type_LUT[transitions[song_index][transList[t_index]]["type"]])
                        data.append(transitions[song_index][transList[t_index]]["stop"])
                        data.extend([transitions[song_index][transList[t_index]]["index"] >> i & 0xff for i in (0,8)])
                        if transitions[song_index][transList[t_index]]["duration"] < 1:  # rounding error on scaling can generate negative / zero values
                            transitions[song_index][transList[t_index]]["duration"] = 1
                        data.extend([transitions[song_index][transList[t_index]]["duration"] >> i & 0xff for i in (0,8)])  # Use index from INIT
                        back_porch = transitions[song_index][transList[t_index+1]]["time"]-transitions[song_index][transList[t_index]]["time"]-transitions[song_index][transList[t_index]]["duration"]
                        if back_porch < 0:   # rounding error on scaling can generate negative values
                            back_porch = 0
                        data.extend([back_porch >> i & 0xff for i in (0,8)])  # Back Porch = duration to first transtion
                        length += 8
    display_text = "Download Songs Complete"
    display_message(display_text)

def CheckSongs():

    global currentTransition, active_tube_value, song, songSelection

    checkComplete = 1
    for tube in range(NUM_TUBES):
        tubeBit = tubes[tube]
        for song_index in range(len(songNames)):
            print "Song [", song_index, "]"
            data = []
            transList = []
            packetCount = 0
            songSize = 0
            for t_index in range(len(transitions[song_index])):
                if (transitions[song_index][t_index]["tubes"] & tubeBit) > 0:
                    transList.append(t_index)
            # First is always an INIT
            if len(transList) > 2:  # Don't slow down writing empty song
                for t_index in range(1, len(transList)):
                    if transitions[song_index][transList[t_index]]["type"] in ["END"]:
                        break
                    elif transitions[song_index][transList[t_index]]["time"] + transitions[song_index][transList[t_index]]["duration"] > transitions[song_index][transList[t_index+1]]["time"]:
                        for local_tube in range(NUM_TUBES):
                            active_tube_value[local_tube].set(0)
                        songSelection.selectitem(songNames[song_index], setentry=1)
                        currentTransition = transList[t_index+1]
                        song = song_index
                        active_tube_value[tube].set(1)
                        updateActiveTubes()
                        trans_time_entry[ACTIVE_COL].configure(fg="red")
                        display_text = "Song %d has an overlap on tube %d at transition %d." % (song_index+1, tube+1, transList[t_index+1])
                        display_message(display_text)
                        checkComplete = 0
                        break
            if checkComplete == 0:
                break
        if checkComplete == 0:
            break
    if checkComplete == 1:
        display_text = "Check Songs Complete"
        display_message(display_text)


def debugSongRead():

    songToRead = 0
    send_song(MOTE14_MAC, songToRead)

def downloadAll():

   downloadScenes()
   downloadSongs()


def file_menu():
   file_btn = tk.Menubutton(menu_frame, text='File', underline=0)
   file_btn.pack(side=tk.LEFT, padx="2m")
   file_btn.menu = tk.Menu(file_btn)
   file_btn.menu.add_command(label="Open", underline=0, command=readFile)
   file_btn.menu.add_command(label="Save", underline=0, command=saveFile)
   file_btn.menu.add_command(label="Print", underline=0, command=printFile)
   file_btn.menu.add_command(label="Download Scenes", underline=0, command=downloadScenes)
   file_btn.menu.add_command(label="Download Songs", underline=0, command=SaveSongs)
   file_btn.menu.add_command(label="Donwload All", underline=0, command=downloadAll)
   file_btn.menu.add_command(label="Debug Song Read", underline=0, command=debugSongRead)
   file_btn.menu.add_command(label="Erase Scenes", underline=0, command=erase_scenes)
   file_btn.menu.add('separator')
   file_btn.menu.add_command(label='Download With Flicker', underline=0, command=downloadFull)
   file_btn.menu.add('separator')
   file_btn.menu.add_command(label='Exit', underline=0, command=file_btn.quit)
   file_btn['menu'] = file_btn.menu
   return file_btn

def edit_menu():
   edit_btn = tk.Menubutton(menu_frame, text='Edit', underline=0)
   edit_btn.pack(side=tk.LEFT, padx="2m")
   edit_btn.menu = tk.Menu(edit_btn)
   edit_btn.menu.add_command(label="Check Songs", underline=0, command=CheckSongs)
   edit_btn.menu.add('separator')
   edit_btn['menu'] = edit_btn.menu
   return edit_btn

def view_menu():
   view_btn = tk.Menubutton(menu_frame, text='View', underline=0,)
   view_btn.pack(side=tk.LEFT, padx="2m")
   view_btn.menu = tk.Menu(view_btn)
   view_btn.menu.add_command(label="Utilities", underline=0, command=show_bsp)
   view_btn.menu.add_command(label="Generation", underline=0, command=show_io_config)
   view_btn['menu'] = view_btn.menu
   return view_btn

def help_menu():
   help_btn = tk.Menubutton(menu_frame, text='Help', underline=0,)
   help_btn.pack(side=tk.LEFT, padx="2m")
   help_btn.menu = tk.Menu(help_btn)
   help_btn.menu.add_command(label="About", underline=0, command=About)
   help_btn['menu'] = help_btn.menu
   return help_btn

def SaveSongs():

    global saveSongs
    global local_root
    global active_song_value
    global active_songs
    global view_window

    local_root = tk.Tk()
    local_root.geometry("200x500")
    local_root.rowconfigure(2, weight=1)
    local_root.columnconfigure(0, weight=1)

#--    root.option_readfile('optionDB')
    local_root.title('Save Songs')
    view_window = tk.Frame(local_root)
    view_window.grid(row=1, column=0, sticky=tk.W+tk.N, padx=0, pady=1)
    Button(view_window, text="Set", width=4, command=SetSaveSongs).grid(row=0, column=0, padx=0)
    Button(view_window, text="Clear", width=4, command=ClearSaveSongs).grid(row=1, column=0, padx=0)
    active_songs = []
    active_song_value = []
    for song in range(len(songNames)):
      active_song_value.append(tk.IntVar())
      active_songs.append(Checkbutton(view_window, text=song+1, variable=active_song_value[song], width=4, anchor=tk.W))
      active_songs[song].grid(row=song+2, column=0, padx=0, pady=1)
    Label(view_window, text="", width=1,  background="white").grid(row=14, column=0)  # Spacer
    ''' Copy '''
    copyRow = 17
    Button(view_window, text="Save", width=6, command=downloadSongs).grid(row=15, column=0, padx=0)
    Button(view_window, text="Cancel", width=6, command=CloseSaveSongs).grid(row=16, column=0, padx=0)
    print active_song_value
    for song in range(len(songNames)):
      print "Before song_vale[", song, "]: ", active_song_value[song].get()
      active_song_value[song].set(1)
      print "After  song_vale[", song, "]: ", active_song_value[song].get()
    print active_song_value
    print "Before main loop"
    local_root.mainloop()
    print "after main loop"


def CloseSaveSongs():
    a = []

def ClearSaveSongs():
   global active_song_value

   for song in range(len(songNames)):
      active_song_value[song].set(0)

def SetSaveSongs():
   global active_song_value

   for song in range(len(songNames)):
      active_song_value[song].set(1)


def About():
   global VersionString
   view_window = tk.Toplevel(root)
   about_text = "Light Tubes version %s \n\nCopyright 2017, 2018, Gordon Charles" % (VersionString)
   tk.Message(view_window,
              text=about_text,
              justify=tk.CENTER,
              anchor=tk.CENTER,
              relief=tk.GROOVE,
              width=250).pack(padx=10, pady=10)

def printFile():
      global scenes, transitions

      print struct.pack('I', len(scenes))
      for index in range(len(scenes)):
         for pixel in range(NUM_PIXELS):
             color = scenes[index][pixel][FLICKER] * pow(2,8*FLICKER) + scenes[index][pixel][RED] * pow(2,8*RED) + scenes[index][pixel][GREEN] * pow(2,8*GREEN) + scenes[index][pixel][BLUE] * pow(2,8*BLUE)
             print 'Red : ', scenes[index][pixel][RED], ' Green : ', scenes[index][pixel][GREEN], ' Blue : ', scenes[index][pixel][BLUE], ' Flicker : ', scenes[index][pixel][FLICKER]
             print 'scene [', index, '][', pixel, '] {0:08x}'.format(color, 'x')
      print scenes


def saveFile():
    global scenes, sceneSpeeds, transitions
    filename = asksaveasfilename(filetypes=[("allfiles","*"),("pythonfiles","*.py")])
    with open(filename, "wb") as binfile:
        filedata = struct.pack('I', Version)
        binfile.write(filedata)
        filedata = struct.pack('I', len(scenes))
        binfile.write(filedata)
        for index in range(len(scenes)):
            filedata = struct.pack('I', sceneSpeeds[index])
            binfile.write(filedata)
            for pixel in range(NUM_PIXELS):
                for comp in range(NUM_COMPS):
                    filedata = struct.pack('I', scenes[index][pixel][comp])
                    binfile.write(filedata)
        for song_index in range(len(songNames)):
            filedata = struct.pack('I', len(transitions[song_index]))
            binfile.write(filedata)
            for t_index in range(len(transitions[song_index])):
                filedata = struct.pack('I', transition_type_LUT[transitions[song_index][t_index]["type"]])
                binfile.write(filedata)
                filedata = struct.pack('I', transitions[song_index][t_index]["stop"])
                binfile.write(filedata)
                filedata = struct.pack('I', transitions[song_index][t_index]["time"])
                binfile.write(filedata)
                filedata = struct.pack('I', transitions[song_index][t_index]["duration"])
                binfile.write(filedata)
                filedata = struct.pack('I', transitions[song_index][t_index]["index"])
                binfile.write(filedata)
                filedata = struct.pack('I', transitions[song_index][t_index]["tubes"])
                binfile.write(filedata)
                filedata = struct.pack('I', transitions[song_index][t_index]["relative"])
                binfile.write(filedata)
                filedata = struct.pack('I', transitions[song_index][t_index]["selection"])
                binfile.write(filedata)
        for mote in range(NUM_MOTES):
            for song_index in range(len(songNames)+1):
                filedata = struct.pack('I', moteFileState[mote][song_index])
                binfile.write(filedata)


def readFile():
   global scenes, sceneSpeeds, transitions, currentScene, currentTransition, songNames
   if sys.platform == 'darwin': # 'darwin' = OS X - filetypes not recognized on MAC
      filename = askopenfilename()
   else:
      filename = askopenfilename(filetypes=[("allfiles","*")])
   with open(filename, "rb") as binfile:
      intsize = struct.calcsize('i')
      filedata = binfile.read(intsize)
      if filedata == '':
          return(-1)
      readVersion = struct.unpack('I', filedata)[0]
      print "Reading file version : ", readVersion
      filedata = binfile.read(intsize)
      if filedata == '':
          return(-1)
      sceneLength = struct.unpack('I', filedata)[0]
      color = [0, 0, 0, 0]
      scenes = []
      sceneSpeeds = []
      for index in range(sceneLength):
         scene = []
         if readVersion > 0: # versions after zero have flicker speed in them
             filedata = binfile.read(intsize)
             if filedata == '':
                 return(-1)
             sceneSpeeds.append(struct.unpack('I', filedata)[0])
         for pixel in range(NUM_PIXELS):
             for comp in range(NUM_COMPS):
                 filedata = binfile.read(intsize)
                 if filedata == '':
                     return(-1)
                 color[comp] = struct.unpack('I', filedata)[0]
             scene.append(list(color))
         scenes.append(list(scene))
         if readVersion == 0: # versions after zero have flicker speed in them
             if isFlicker(len(scenes)-1):
                 sceneSpeeds.append(9)
             else:
                 sceneSpeeds.append(0)
      workingTransition = transition.copy()
      if readVersion > 1:  # versions after one have 12 song files
          NumSongsInFile = len(songNames)
      else:
          NumSongsInFile = 4
      for song_index in range(NumSongsInFile):
          filedata = binfile.read(intsize)
          if filedata == '':
             return(-1)
          transLength = struct.unpack('I', filedata)[0]
          songList = []
          for t_index in range(transLength):
              filedata = binfile.read(intsize)
              if filedata == '':
                 return(-1)
              workingTransition["type"] = trans_type_rev_LUT[struct.unpack('I', filedata)[0]]
              filedata = binfile.read(intsize)
              if filedata == '':
                 return(-1)
              workingTransition["stop"] = struct.unpack('I', filedata)[0]
              filedata = binfile.read(intsize)
              if filedata == '':
                 return(-1)
              workingTransition["time"] = struct.unpack('I', filedata)[0]
              filedata = binfile.read(intsize)
              if filedata == '':
                 return(-1)
              workingTransition["duration"] = struct.unpack('I', filedata)[0]
              filedata = binfile.read(intsize)
              if filedata == '':
                 return(-1)
              workingTransition["index"] = struct.unpack('I', filedata)[0]
              filedata = binfile.read(intsize)
              if filedata == '':
                 return(-1)
              workingTransition["tubes"] = struct.unpack('I', filedata)[0]
              filedata = binfile.read(intsize)
              if filedata == '':
                 return(-1)
              workingTransition["relative"] = struct.unpack('I', filedata)[0]
              filedata = binfile.read(intsize)
              if filedata == '':
                 return(-1)
              workingTransition["selection"] = struct.unpack('I', filedata)[0]
              songList.append(workingTransition.copy())
          transitions[song_index] = list(songList)  # Changed to support reading of files with 4 songs into version 2 format
      for mote in range(NUM_MOTES):
          for song_index in range(len(songNames)+1):
              filedata = binfile.read(intsize)
              if filedata == '':
                 return(-1)
              moteFileState[mote][song_index] = struct.unpack('I', filedata)[0]
   currentTransition = 0
   currentScene = 0
   loadScenes(currentScene)
   loadTransitions(currentTransition)


def display_message(message):
   message_box = tk.Toplevel()
   message_box.title("Information:")

   msg = tk.Message(message_box, text=message, width=500)
   msg.pack()

   close_button = tk.Button(message_box, text="Close", command=message_box.destroy)
   close_button.pack()

def show_io_config():
   global canvas, mode_frame, info_frame, vscrollbar
   util_frame.grid_remove()
   canvas.grid()
   vscrollbar.grid()
   mode_frame.grid()

def show_bsp():
   global canvas, mode_frame, finfo_frame, vscrollbar
   canvas.grid_remove()
   vscrollbar.grid_remove()
   mode_frame.grid_remove()
   util_frame.grid()


def dust_crc(int_list):
   c = []
   new_crc = []
   for index in range(16):
      c.append(0)
      new_crc.append(0)
   for byte in int_list:
      d = gen_bits(byte)
      new_crc[0] = (d[4] + d[0] + c[8] + c[12]) % 2
      new_crc[1] = (d[5] + d[1] + c[9] + c[13]) % 2
      new_crc[2] = (d[6] + d[2] + c[10] + c[14]) % 2
      new_crc[3] = (d[7] + d[3] + c[11] + c[15]) % 2
      new_crc[4] = (d[4] + c[12]) % 2
      new_crc[5] = (d[5] + d[4] + d[0] + c[8] + c[12] + c[13]) % 2
      new_crc[6] = (d[6] + d[5] + d[1] + c[9] + c[13] + c[14]) % 2
      new_crc[7] = (d[7] + d[6] + d[2] + c[10] + c[14] + c[15]) % 2
      new_crc[8] = (d[7] + d[3] + c[0] + c[11] + c[15]) % 2
      new_crc[9] = (d[4] + c[1] + c[12]) % 2
      new_crc[10] = (d[5] + c[2] + c[13]) % 2
      new_crc[11] = (d[6] + c[3] + c[14]) % 2
      new_crc[12] = (d[7] + d[4] + d[0] + c[4] + c[8] + c[12] + c[15]) % 2
      new_crc[13] = (d[5] + d[1] + c[5] + c[9] + c[13]) % 2
      new_crc[14] = (d[6] + d[2] + c[6] + c[10] + c[14]) % 2
      new_crc[15] = (d[7] + d[3] + c[7] + c[11] + c[15]) % 2
      temp = d[7] + d[3] + c[7] + c[11] + c[15]
      for index in range(16):
         c[index] = new_crc[index]
   crc_as_int = 0
   for index in range(16):
      crc_as_int += c[index] << index
   return crc_as_int

''' Tube functions '''
def color2Text(components):
    redHex   = '{0:02x}'.format(components[0], 'x')
    greenHex = '{0:02x}'.format(components[1], 'x')
    blueHex  = '{0:02x}'.format(components[2], 'x')
    textColor = "#" + redHex + greenHex + blueHex
    return textColor

def updateActiveTubes():
    global tube_bit_field, active_tube_value, currentTransition, scenes

    tube_bit_field = 0
    for i in range(len(active_tube_value)):
        if active_tube_value[i].get() == 1:
            tube_bit_field += 2 ** i
    loadTransitions(currentTransition)
    loadScenes(len(scenes)-2)

def ClearTubes():

   for tube in range(NUM_TUBES):
      active_tube_value[tube].set(0)
   updateActiveTubes()

def SetTubes():
   for tube in range(NUM_TUBES):
      active_tube_value[tube].set(1)
   updateActiveTubes()

def updateRed(event):
    global redHex, greenHex, blueHex
    redHex  = '{0:02x}'.format(CompComp(int(event)), 'x')
    color = "#" + redHex + greenHex + blueHex
    displayColor.configure(bg=color)

def updateGreen(event):
    global redHex, greenHex, blueHex
    greenHex  = '{0:02x}'.format(CompComp(int(event)), 'x')
    color = "#" + redHex + greenHex + blueHex
    displayColor.configure(bg=color)

def updateBlue(event):
    global redHex, greenHex, blueHex
    blueHex  = '{0:02x}'.format(CompComp(int(event)), 'x')
    color = "#" + redHex + greenHex + blueHex
    displayColor.configure(bg=color)

def selectPalleteColor(palette_row, palette_col):
    global redHex, greenHex, blueHex, palette_color, redScale, greenScale, blueScale
    color = color2Text(ColorComp([palette_color[palette_row][palette_col][RED], palette_color[palette_row][palette_col][GREEN],palette_color[palette_row][palette_col][BLUE],0]))
    displayColor.configure(bg=color)
    redScale.set(palette_color[palette_row][palette_col][RED])
    greenScale.set(palette_color[palette_row][palette_col][GREEN])
    blueScale.set(palette_color[palette_row][palette_col][BLUE])


def selectPixelColor(pixel, *args):
    global palette_color, pixels, pixel_tk_img, pixel_select, redScale, greenScale, blueScale, flickerScale, pixel_color, trans_flicker, pixel_blank

    for i in range(pixel_img[pixel].size[0]):
        for j in range(pixel_img[pixel].size[1]):
            pixels[pixel][i,j] = (CompComp(redScale.get()), CompComp(greenScale.get()), CompComp(blueScale.get()))
    pixel_tk_img[pixel] = ImageTk.PhotoImage(pixel_img[pixel])
    pixel_select[pixel].config(image=pixel_tk_img[pixel])
    if trans_flicker[pixel].get() == '':
        pixel_color[pixel] = [redScale.get(), greenScale.get(), blueScale.get(), flickerScale.get()]
        trans_flicker[pixel].delete(0, END)
        trans_flicker[pixel].insert(0, flickerScale.get())
    else:
        pixel_color[pixel] = [redScale.get(), greenScale.get(), blueScale.get(), int(trans_flicker[pixel].get())]
    pixel_blank[pixel] = False

def revSelectPixelColor(pixel, *args):
    global palette_color, pixels, pixel_tk_img, pixel_select, redScale, greenScale, blueScale, flickerScale, pixel_color, trans_flicker, pixel_blank

    redScale.set(pixel_color[pixel][RED])
    greenScale.set(pixel_color[pixel][GREEN])
    blueScale.set(pixel_color[pixel][BLUE])
    flickerScale.set(pixel_color[pixel][FLICKER])

def selectSceneColor(index, pixel, *args):
    global redScale, greenScale, blueScale, flickerScale, pixel_color, currentScene

    selectedIndex = currentScene - 1 + index
    if selectedIndex > 0 and selectedIndex < len(scenes):
        redScale.set(scenes[selectedIndex][pixel][RED])
        greenScale.set(scenes[selectedIndex][pixel][GREEN])
        blueScale.set(scenes[selectedIndex][pixel][BLUE])
        flickerScale.set(scenes[selectedIndex][pixel][FLICKER])

def initReset():
    global transitions, song, transition, scenes, transition_stop, trans_stop_LUT, trans_stop_rev_LUT, moteFileState, musicStartTime, musicTime, sceneSpeeds

    transitions = []
    transition["type"]     = "INIT"
    transition["stop"]     = 0
    transition["time"]     = 0
    transition["duration"] = 0
    transition["scene"]    = 1
    transition["tubes"]    = ALL_TUBES

    songList = []  # Added May 27, 2018 seems like it should be here
    songList.append(transition.copy())

    transition["type"]     = "END"
    transition["stop"]     = 0
    transition["time"]     = 10
    transition["duration"] = 0
    transition["scene"]    = 0
    transition["tubes"]    = ALL_TUBES

    songList.append(transition.copy())

    for i in range(len(songNames)):
       transitions.append(list(songList))
    scenes = []
    sceneSpeeds = []
    speedValue = 0
    scene = []
    for pixel in range(NUM_PIXELS):
        color = [0, 0, 0, 0]
        scene.append(list(color))
    scenes.append(list(scene))
    sceneSpeeds.append(0)

    transition_stop.append(" ")
    trans_stop_LUT[" "] = 0
    trans_stop_rev_LUT[0] = " "
    for pixel in range(0, NUM_PIXELS):
        selectItem = "Stop " + str(pixel+1)
        transition_stop.append(selectItem)
        trans_stop_LUT[selectItem] = pixel+1
        trans_stop_rev_LUT[pixel+1]  = selectItem

    for pixel in range(0, NUM_PIXELS):
        selectItem = "Start " + str(pixel+1)
        transition_stop.append(selectItem)
        trans_stop_LUT[selectItem]    = pixel + 128 + 1
        trans_stop_rev_LUT[pixel+128+1] = selectItem

    for i in range(len(songNames)):
        songLUT[songNames[i]] = i

    moteFileState = []
    for mote in range(len(macIDs)):
        songFileState = []
        for song_index in range(len(songNames)+1):  # Use song_index 0 for scene state
            songFileState.append(2)
        songFileState[0] = 0
        moteFileState.append(list(songFileState))

def ClearAll():
    initReset()
    loadTransitions(0)
    loadScenes(0)



def loadScenes(index):
    global scenes, sceneSpeeds, scenes_index, scenes_tubes, scene_flicker, scenes_speed, sceneUpdating

    if (index <0 ) or (index+1 > len(scenes)):
        print "Function loadScenes, index out of bounds"
    else:
        sceneUpdating = True
        for pixel in range(NUM_PIXELS):
            scenes_tubes[1][pixel].configure(bg=color2Text(ColorComp(scenes[index][pixel])))
            scene_flicker[pixel].configure(text=scenes[index][pixel][FLICKER])
            if (index+1 < len(scenes)):
                scenes_tubes[2][pixel].configure(bg=color2Text(ColorComp(scenes[index+1][pixel])))
            else:
                scenes_tubes[2][pixel].configure(bg="gray90")
            if (index > 0):
                scenes_tubes[0][pixel].configure(bg=color2Text(ColorComp(scenes[index-1][pixel])))
            else:
                scenes_tubes[0][pixel].configure(bg="gray90")
        for i in range(3):
            scenes_index[i].delete(0, END)
        scenes_index[1].insert(0, index)
        scenes_speed[1].set(sceneSpeeds[index])
        if (index > 0):
            scenes_index[0].insert(0, index-1)
            scenes_speed[0].set(sceneSpeeds[index-1])
        if (index + 1 < len(scenes)):
            scenes_index[2].insert(0, index+1)
            scenes_speed[2].set(sceneSpeeds[index+1])
        sceneUpdating = False

def scenesRight():
    global scenes, currentScene

    if (len(scenes) - currentScene) > 2:
        currentScene += 1
        loadScenes(currentScene)


def scenesLeft():
    global scenes, currentScene

    print "Left Current Scene : ", currentScene
    if currentScene > 0:
        currentScene -= 1
        loadScenes(currentScene)


def displayTime(time_val):

    time_text  = '{0:06d}'.format(time_val, 'd')
    numSeconds = int((time_val/100)) % 60
    numMinutes = int((int((time_val/100)) - numSeconds)/60)
    secondsText = '{0:02d}'.format(numSeconds, 'd')
    minutesText = '{0:02d}'.format(numMinutes, 'd')
    time_text = minutesText + ":" + secondsText + "." + time_text[4:]
    return(time_text)

def minutes2Miliseconds(time_val):

    tensOfMiliseconds = time_val % 10000 + int(time_val/10000)*6000
    return(tensOfMiliseconds)

def time2Miliseconds(time_string):

    time = int(time_string[0:2])*6000 + int(time_string[2:])
    return time

def tubeMatch(transition):
    global transitions, song, tube_bit_field

    #print "tube bit field : ", tube_bit_field, " transitions[transition][tubes]", transitions[transition]["tubes"]
    if tube_bit_field == ALL_TUBES:
        return True
    else:
        if transitions[song][transition]["tubes"] == tube_bit_field:
            return True
        else:
            return False


def inTube(local_tube_bit_field, transition):
    global transitions, song

    if (transitions[song][transition]["tubes"] & local_tube_bit_field) > 0:
        return True
    else:
        return False


def loadTransitions(transition):
    global trans_sel, trans_sel_value, trans_num, trans_time, trans_type, trans_stop, trans_stop_rev_LUT, trans_duration, trans_index, trans_scene, trans_pixels, trans_flicker, pixel_blank
    global transitions, song, scenes, trans_sel_low, trans_sel_high, trans_radio_var, trans_time_entry, updating, tubeExclusive, trans_speed


    if (transition < 0 ) or (transition+1 > len(transitions[song])):
        print "Function loadTransitions, index out of bounds"
    else:
        updating = True
        ''' transitions occuring before insertion point '''
        transition_list = []
        transition_ptr = transition
        while len(transition_list) < ACTIVE_COL and transition_ptr >= 0:
            if tubeExclusive.get() == 0 and inTube(tube_bit_field, transition_ptr):
                transition_list.insert(0, transition_ptr)
            elif tubeExclusive.get() == 1 and transitions[song][transition_ptr]["tubes"] == tube_bit_field:
                transition_list.insert(0, transition_ptr)
            transition_ptr -= 1
        threshold   = ACTIVE_COL-len(transition_list)
        for index in range(0, threshold):
            trans_sel_value[index].set(0)
            trans_num[index].delete(0, END)
            trans_time[index].set("")
            trans_type[index].select_set(0)
            trans_stop[index].select_set(0)
            trans_duration[index].set("")
            trans_index[index].set("")
            for pixel in range(NUM_PIXELS):
                trans_scene[index][pixel].configure(bg="gray90")
            for tube in range(NUM_TUBES):
                trans_radio_var[index][tube].set(0)
        for index in range (threshold, ACTIVE_COL):
            t_index = transition_list[index-threshold]
            if transitions[song][t_index]["selection"] == 1:
                trans_sel_value[index].set(1)
            else:
                trans_sel_value[index].set(0)
            trans_index[index].set(t_index)
            trans_num[index].delete(0, END)
            trans_num[index].insert(0, t_index)
            trans_time[index].set(displayTime(transitions[song][t_index]["time"]))
            if (transitions[song][t_index]["relative"] == 0):
                trans_time_entry[index].configure(fg="blue")
            else:
                trans_time_entry[index].configure(fg="black")
            trans_type[index].selectitem(transitions[song][t_index]["type"], setentry=1)
            trans_stop[index].selectitem(trans_stop_rev_LUT[transitions[song][t_index]["stop"]], setentry=1)
            trans_duration[index].set(displayTime(transitions[song][t_index]["duration"]))
            trans_index[index].set(transitions[song][t_index]["index"])
            for pixel in range(NUM_PIXELS):
                color = color2Text(ColorComp(scenes[transitions[song][t_index]["index"]][pixel]))
                trans_scene[index][pixel].configure(bg=color)
            for tube in range(NUM_TUBES):
                if (transitions[song][t_index]["tubes"] & (1 << tube) > 0):
                    trans_radio_var[index][tube].set(1)
                else:
                    trans_radio_var[index][tube].set(0)
        ''' transition occuring after insertion point '''
        transition_ptr = transition + 1
        while transition_ptr < (len(transitions[song])-1) and tubeMatch(transition_ptr) == False:
            transition_ptr += 1
        if transitions[song][currentTransition+1]["type"] == "END":
            trans_sel_value[NUM_COL-1].set(0)
        if transitions[song][currentTransition+1]["selection"] == 1:
            trans_sel_value[NUM_COL-1].set(1)
        else:
            trans_sel_value[NUM_COL-1].set(0)
        trans_num[NUM_COL-1].delete(0, END)
        trans_num[NUM_COL-1].insert(0, transition_ptr)
        trans_time[NUM_COL-1].set(displayTime(transitions[song][transition_ptr]["time"]))
        trans_type[NUM_COL-1].selectitem(transitions[song][transition_ptr]["type"], setentry=1)
        trans_stop[NUM_COL-1].selectitem(trans_stop_rev_LUT[transitions[song][transition_ptr]["stop"]], setentry=1)
        trans_duration[NUM_COL-1].set(displayTime(transitions[song][transition_ptr]["duration"]))
        trans_index[NUM_COL-1].set(transitions[song][transition_ptr]["index"])
        for pixel in range(NUM_PIXELS):
            color = color2Text(ColorComp(scenes[transitions[song][transition_ptr]["index"]][pixel]))
            trans_scene[NUM_COL-1][pixel].configure(bg=color)
        for tube in range(NUM_TUBES):
            if (transitions[song][transition_ptr]["tubes"] & (1 << tube) > 0):
                trans_radio_var[NUM_COL-1][tube].set(1)
            else:
                trans_radio_var[NUM_COL-1][tube].set(0)
    updating = False


def findScene(find_scene, speed):
    global scenes

    for index in range(len(scenes)):
        if (scenes[index] == find_scene) and (sceneSpeeds[index] == speed):
            return(index)
    return(-1)


def CompComp(component):

    adjComp   = 255 - int(((255-component) * (255-component) * (255-component))/(255*255))
    return(adjComp)

def ColorComp(components):

    adjComps = []
    for i in range(3):
        adjComps.append(255 - int(((255-components[i]) * (255-components[i]) * (255-components[i]))/(255*255)))
    adjComps.append(components[3])
    return(adjComps)


def setActiveScene(index):
    global scenes, pixels, pixel_tk_img, pixel_color, trans_flicker, pixel_blank, currentScene

    sceneIndex = currentScene - 1 + index
    if sceneIndex in range(len(scenes)):
        for pixel in range(NUM_PIXELS):
            for i in range(pixel_img[pixel].size[0]):
               for j in range(pixel_img[pixel].size[1]):
                   pixels[pixel][i,j] = (CompComp(scenes[sceneIndex][pixel][RED]), CompComp(scenes[sceneIndex][pixel][GREEN]), CompComp(scenes[sceneIndex][pixel][BLUE]))
            pixel_tk_img[pixel] = ImageTk.PhotoImage(pixel_img[pixel])
            pixel_select[pixel].config(image=pixel_tk_img[pixel])
            pixel_color[pixel] = scenes[sceneIndex][pixel]
            pixel_blank[pixel] = False
            trans_flicker[pixel].delete(0, END)
            if scenes[sceneIndex][pixel][FLICKER] > 0:
                trans_flicker[pixel].insert(0, scenes[sceneIndex][pixel][FLICKER])


def addScene():
    global scenes, pixel_color, sceneSpeeds, speedValue

    scenes.append(list(pixel_color))
    if isFlicker(len(scenes)-1):
        if speedValue == 0:
           sceneSpeeds.append(9)
        else:
           sceneSpeeds.append(speedValue)
    else:
        sceneSpeeds.append(0)

def clearScene():
    global trans_flicker, pixel_blank, pixel_color, pixel_tk_img, pixels


    for pixel in range(NUM_PIXELS):
        pixel_color[pixel] = [0, 0, 0, 0]
        for i in range(pixel_img[pixel].size[0]):
            for j in range(pixel_img[pixel].size[1]):
                pixels[pixel][i,j] = (0, 0, 0)
        pixel_tk_img[pixel] = ImageTk.PhotoImage(pixel_img[pixel])
        pixel_select[pixel].config(image=pixel_tk_img[pixel])
        trans_flicker[pixel].delete(0, END)
        pixel_blank[pixel] = True


def fillScene():
    global trans_flicker, pixel_blank, pixel_color, pixel_tk_img, pixels


    colorPoint = []
    colorPosition = []
    for pixel in range(NUM_PIXELS):
        if not pixel_blank[pixel]:
            colorPoint.append(pixel_color[pixel])
            colorPosition.append(pixel)
    if len(colorPoint) > 0:
        if colorPosition[0] > 0:
            colorPoint.insert(0, colorPoint[0])
            colorPosition.insert(0, 0)
        if colorPosition[len(colorPosition)-1] < NUM_PIXELS-1:
            colorPoint.insert(len(colorPosition)-1, colorPoint[len(colorPosition)-1])
            colorPosition.insert(len(colorPosition), 29)
        for k in range(len(colorPosition)-1):
            delta = []
            deltaX = colorPosition[k+1]-colorPosition[k]
            for comp in range(NUM_COMPS):
                delta.append(colorPoint[k+1][comp]-colorPoint[k][comp])
            for pixel in range(0, deltaX+1):
                activePixel = colorPosition[k]+pixel
                fillColor = []
                for comp in range(NUM_COMPS):
                    fillColor.append(colorPoint[k][comp] + int(pixel * delta[comp]/deltaX))
                pixel_color[activePixel] = [fillColor[0], fillColor[1], fillColor[2], fillColor[3]]
                for i in range(pixel_img[activePixel].size[0]):
                    for j in range(pixel_img[activePixel].size[1]):
                        pixels[activePixel][i,j] = (pixel_color[activePixel][RED], pixel_color[activePixel][GREEN], pixel_color[activePixel][BLUE])
                pixel_tk_img[activePixel] = ImageTk.PhotoImage(pixel_img[activePixel])
                pixel_select[activePixel].config(image=pixel_tk_img[activePixel])
                trans_flicker[activePixel].delete(0, END)
                trans_flicker[activePixel].insert(0, fillColor[3])
                pixel_blank[activePixel] = False


def insertRelativeDelay(insertAfterTransition, timeShift):
    global trans_num, trans_time, trans_type, trans_stop, trans_duration, trans_index, trans_scene, trans_pixels, trans_flicker, pixel_blank
    global transitions, song, scenes, currentTransition

    #Form list of later relative transitions until the first absolute transition time
    relativeTransList = []
    maxTime = 10000000
    maxTimeTransition = len(transitions[song])-1
    for t_index in range(insertAfterTransition+1, len(transitions[song])-1):
        if inTube(tube_bit_field, t_index) and transitions[song][t_index]["relative"] == 0:
            maxTime = transitions[song][t_index]["time"]
            maxTimeTransition = t_index
            break
        elif inTube(tube_bit_field, t_index) and transitions[song][t_index]["relative"] == 1:
            relativeTransList.append(t_index)
    if len(relativeTransList) > 0:
        for r_index in range(len(relativeTransList)):
            if (transitions[song][relativeTransList[r_index]]["tubes"] & transitions[song][insertAfterTransition]["tubes"] > 0):
                transitions[song][relativeTransList[r_index]]["time"] += timeShift
        if transitions[song][relativeTransList[len(relativeTransList)-1]]["time"] > maxTime:
            display_text = "Ineserting time has created a conflict at transition %d." % (maxTimeTransition)
            display_message(display_text);
    transitions[song][len(transitions[song])-1]["time"] = transitions[song][len(transitions[song])-2]["time"] + transitions[song][len(transitions[song])-2]["duration"]


def addTransition():
    global trans_num, trans_time, trans_type, trans_stop, trans_stop_LUT, trans_duration, trans_index, trans_scene, trans_pixels, trans_flicker, pixel_blank
    global transitions, song, scenes, currentTransition, currentScene, trans_speed, speedValue

    time_text = re.sub("[^0-9]", "", trans_time[ACTIVE_COL].get())
    if time_text == "":
        time_val = 0
    else:
        time_val = minutes2Miliseconds(int(time_text))
    duration_text = re.sub("[^0-9]", "", trans_duration[ACTIVE_COL].get())
    if duration_text == "":
        duration_val = 0
    else:
        duration_val = minutes2Miliseconds(int(duration_text))
    scene_text = re.sub("[^0-9]", "", trans_index[ACTIVE_COL].get())
    if scene_text == "":
        scene_val = -1
    else:
        scene_val = int(scene_text)
    if scene_val > (len(scenes)-1):
        display_text = "Index value %d is larger than the number of Scenes %d." % (scene_val, len(scenes)-1)
        display_message(display_text);
    elif time_text == '' and not (trans_type[ACTIVE_COL].get() == "INIT"):
        display_message("Time must be entered for all transitions, except INIT")
    elif trans_type[ACTIVE_COL].get() == '':
        display_message("Type must be entered for all transitions")
    elif duration_text == "" and not (trans_type[ACTIVE_COL].get() == "INIT"):
        display_message("Duration must be greater than zero")
    elif trans_stop[ACTIVE_COL].get() == '' and (trans_type[ACTIVE_COL].get() == "SW UP" or trans_type[ACTIVE_COL].get() == "SW DN"):
        display_message("Stop value required for SW UP and SW DN types")
    elif trans_type[ACTIVE_COL].get() == "INIT":
        for t_index in range(len(transitions[song])):
            if transitions[song][t_index]["type"] == "INIT":
                if tubeMatch(t_index):
                    if scene_val > 0:
                        transitions[song][t_index]["index"] = scene_val
                    else:
                        if (findScene(pixel_color, 0) == -1):
                            transitions[song][t_index]["index"] = len(scenes)
                            addScene()
                        else:
                            transitions[song][t_index]["index"] = findScene(pixel_color, 0)
                    break
                else:
                    transitions[song][t_index]["tubes"] = transitions[song][t_index]["tubes"] & ~tube_bit_field
            else:
                currentTransition += 1
                transitions[song].insert(t_index, transition.copy())  # transition should always be initialized to zeroed values
                transitions[song][t_index]["tubes"]    = tube_bit_field
                transitions[song][t_index]["time"]     = 0
                transitions[song][t_index]["duration"] = 0
                transitions[song][t_index]["stop"]     = 0
                transitions[song][t_index]["type"]     = "INIT"
                if scene_val > 0:
                    transitions[song][t_index]["index"] = scene_val
                else:
                    if (findScene(pixel_color, speedValue) == -1):
                        addScene()
                        transitions[song][t_index]["index"] = len(scenes)
                    else:
                        transitions[song][t_index]["index"] = findScene(pixel_color, speedValue)
                break
        loadTransitions(currentTransition)
        loadScenes(len(scenes)-2)
    else:
        t_index = 0
        for t_index in range(currentTransition, 0, -1):
            print "addTubes t_index :", t_index
            if inTube(tube_bit_field, t_index):
                break
        currentTransition = t_index
        print "addTubes t_index :", t_index, "Current Transtiion : ", currentTransition
        if len(time_text) < 6:
            time_delta = time_val + duration_val
            time_val += transitions[song][t_index]["time"] + transitions[song][t_index]["duration"]  # if the user enters less than the full time calculate time as a delta
            transition_relative = 1
        else:
            time_delta = time_val - (transitions[song][t_index]["time"] + transitions[song][t_index]["duration"]) + duration_val
            transition_relative = 0
        currentTransition += 1
        while transitions[song][currentTransition]["time"] < time_val and not transitions[song][currentTransition]["type"] == "END":
           currentTransition += 1
        transitions[song].insert(currentTransition, transition.copy())
        transitions[song][currentTransition]["duration"] = duration_val
        transitions[song][currentTransition]["type"]     = trans_type[ACTIVE_COL].get()
        transitions[song][currentTransition]["tubes"]    = tube_bit_field
        transitions[song][currentTransition]["time"]     = time_val
        transitions[song][currentTransition]["relative"] = transition_relative
        insertRelativeDelay(currentTransition, time_delta)
        transitions[song][len(transitions[song])-1]["time"]    = transitions[song][len(transitions[song])-2]["time"] + transitions[song][len(transitions[song])-2]["duration"]# set END time to end of last transition
        if trans_stop[ACTIVE_COL].get() == '' or not (transitions[song][currentTransition]["type"] == "SW UP" or transitions[song][currentTransition]["type"] == "SW DN"):
            print "set to zero"
            print "trasn type : ", transitions[song][currentTransition]["type"]
            print "stop setting : ", trans_stop[ACTIVE_COL].get()
            transitions[song][currentTransition]["stop"]     = 0
        else:
            transitions[song][currentTransition]["stop"]     = trans_stop_LUT[trans_stop[ACTIVE_COL].get()]
        if scene_val in range(len(scenes)):
            transitions[song][currentTransition]["index"] = scene_val
        else:
            if (findScene(pixel_color, speedValue) == -1):
                transitions[song][currentTransition]["index"] = len(scenes)
                addScene()
            else:
                transitions[song][currentTransition]["index"] = findScene(pixel_color, speedValue)
        print transitions[song]
        loadTransitions(currentTransition)
        currentScene = len(scenes)-2
        loadScenes(currentScene)


def transRight():
    global transitions, song, tube_bit_field, currentTransition

    if len(transitions[song]) - currentTransition > 2:
        currentTransition += 1
        loadTransitions(currentTransition)


def transLeft():
    global transitions, song, tube_bit_field, currentTransition

    if currentTransition > 0:
        currentTransition -= 1
        loadTransitions(currentTransition)


def ffTransRight():
    global transitions, song, tube_bit_field, currentTransition

    if len(transitions[song]) - currentTransition > 10:
        currentTransition += 8
        loadTransitions(currentTransition)
    elif len(transitions[song]) - currentTransition > 2:
        currentTransition += (len(transitions[song]) - currentTransition - 2)
        loadTransitions(currentTransition)


def ffTransLeft():
    global transitions, song, tube_bit_field, currentTransition

    if currentTransition > 14:
        currentTransition -= 8
        loadTransitions(currentTransition)
    elif currentTransition > 6:
        currentTransition = 6
        loadTransitions(currentTransition)


def goToEndofTrans():
    global transitions, song, tube_bit_field, currentTransition

    if len(transitions[song]) - currentTransition > 2:
        currentTransition = len(transitions[song]) - 2
        loadTransitions(currentTransition)


def goToStartofTrans():
    global transitions, song, tube_bit_field, currentTransition

    if currentTransition > 6:
        currentTransition = 6
        loadTransitions(currentTransition)

def ChangeTube(displayCol, tubeNumber,  *args):
    global trans_time, currentTransition, transitions, song, trans_tube, trans_radio_var

    trans_radio_var[displayCol][tubeNumber].set(0)
    displayTransition = int(trans_num[displayCol].get())
    transitions[song][displayTransition]["tubes"] = transitions[song][displayTransition]["tubes"] ^ tubes[tubeNumber]
    loadTransitions(currentTransition)


def ChangeTransitionTime(displayCol, *args):
    global trans_time, updating, currentTransition, transitions, song

    if not updating and not (displayCol == ACTIVE_COL):
        duration_text = re.sub("[^0-9]", "", trans_duration[displayCol].get())
        if len(duration_text) == 6:
            displayTransition = int(trans_num[displayCol].get())
            if displayTransition > 0 and displayTransition < len(transitions[song]):
                if not (time2Miliseconds(duration_text) == transitions[song][displayTransition]["duration"]):
                    delta_time = time2Miliseconds(duration_text)-transitions[song][displayTransition]["duration"]
                    transitions[song][displayTransition]["duration"] = time2Miliseconds(duration_text)
                    insertRelativeDelay(displayTransition, delta_time)
                    loadTransitions(currentTransition)

def ChangeTime(displayCol, *args):
    global trans_time, updating, currentTransition, transitions, song

    if not updating and not (displayCol == ACTIVE_COL):
        time_text = re.sub("[^0-9]", "", trans_time[displayCol].get())
        if len(time_text) == 6:
            displayTransition = int(trans_num[displayCol].get())
            if displayTransition > 0 and displayTransition < len(transitions[song]):
                if not (time2Miliseconds(time_text) == transitions[song][displayTransition]["time"]):
                    delta_time = time2Miliseconds(time_text)-transitions[song][displayTransition]["time"]
                    transitions[song][displayTransition]["time"] = time2Miliseconds(time_text)
                    insertRelativeDelay(displayTransition, delta_time)
                    loadTransitions(currentTransition)

def ChangeScene(displayCol, *args):
    global trans_time, updating, currentTransition, transitions, song, scenes

    if not updating and not (displayCol == ACTIVE_COL):
        scene_text = re.sub("[^0-9]", "", trans_index[displayCol].get())
        if len(scene_text) > 0:
            scene_val = int(scene_text)
            if scene_val in range(len(scenes)):
                displayTransition = int(trans_num[displayCol].get())
                if displayTransition > 0 and displayTransition < len(transitions[song]):
                    transitions[song][displayTransition]["index"] = scene_val
                    loadTransitions(currentTransition)

def ChangeSpeed(displayCol, *args):
    global sceneSpeeds, sceneUpdating, currentScene, transitions, song, scenes, scenes_speed

    if not sceneUpdating:
        speed_text = re.sub("[^0-9]", "", scenes_speed[displayCol].get())
        if len(speed_text) > 0:
            speed_val = int(speed_text)
            if speed_val in range(NUM_FLICKER_SPEEDS):
                displayScene = int(scenes_index[displayCol].get())
                if displayScene > 0 and displayScene < len(scenes):
                    sceneSpeeds[displayScene] = speed_val
                    loadScenes(currentScene)

def ChangeSpeedVal( *args):
    global sceneSpeeds, sceneUpdating, currentScene, transitions, song, scenes, scenes_speed, speedVal, speedValue

    if not sceneUpdating:
        speed_text = re.sub("[^0-9]", "", speedVal.get())
        if len(speed_text) > 0:
            speed_val = int(speed_text)
            if speed_val in range(NUM_FLICKER_SPEEDS):
                speedValue = speed_val
            else:
                display_text = "speed value must be between 0 and 16"
                display_message(display_text)


def ChangeStop(displayCol, *args):
    global updating, currentTransition, transitions, song, trans_stop

    if not updating and not (displayCol == ACTIVE_COL):
        displayTransition = int(trans_num[displayCol].get())
        if displayTransition > 0 and displayTransition < len(transitions[song]):
            if transitions[song][displayTransition]["type"] in ["SW UP", "SW DN"]:
                transitions[song][displayTransition]["stop"] = trans_stop_LUT[trans_stop[displayCol].get()]
            else:
                transitions[song][displayTransition]["stop"] = 0
            loadTransitions(currentTransition)

def ChangeType(displayCol, *args):
    global updating, currentTransition, transitions, song, transition_type

    if not updating and not (displayCol == ACTIVE_COL):
        displayTransition = int(trans_num[displayCol].get())
        if displayTransition > 0 and displayTransition < len(transitions[song]):
            print "Transition Type Pre Mod : ", transitions[song][displayTransition]["type"]
            transitions[song][displayTransition]["type"] = trans_type[displayCol].get()
            print "Transition Type Pros Mod : ", transitions[song][displayTransition]["type"], "  trans_type : ", trans_type[displayCol].get()
            if (transitions[song][displayTransition]["type"] in ["SW UP", "SW DN"]) and transitions[song][displayTransition]["stop"] == 0:
                transitions[song][displayTransition]["stop"] = 1
            if not (transitions[song][displayTransition]["type"] in ["SW UP", "SW DN"]):
                transitions[song][displayTransition]["stop"] = 0
            loadTransitions(currentTransition)

def updateSelection(displayCol, *args):
    global trans_sel_value, transitions, song, selectionStart, selectionEnd, selStartTimeVar, selEndTimeVar, selStartTime, selEndTime, scaleTime, scalePercentage

    if trans_sel_value[NUM_COL-1].get() == 1 and transitions[song][currentTransition+1]["type"]  == "END":
        trans_sel_value[NUM_COL-1].set(0)
    selectionTransition = int(trans_num[displayCol].get())
    if selectionTransition in range(len(transitions[song])):
        if trans_sel_value[displayCol].get() == 1:
            transitions[song][selectionTransition]["selection"] = 1
        else:
            transitions[song][selectionTransition]["selection"] = 0
    else:
        trans_sel_value[displayCol].set(0)
    selectionStart.delete(0, END)
    selStartTimeVar.set("")
    startIndex = len(transitions[song])-1
    for t_index in range(len(transitions[song])):
        if transitions[song][t_index]["selection"] == 1:
            selectionStart.insert(0, t_index)
            startIndex        = t_index
            selStartTime = transitions[song][t_index]["time"]
            selStartTimeVar.set(displayTime(selStartTime))
            break
    selectionEnd.delete(0, END)
    selEndTimeVar.set("")
    endIndex = 0
    for t_index in range(len(transitions[song])-1, -1, -1):
        if transitions[song][t_index]["selection"] == 1:
            selectionEnd.insert(0, t_index)
            endIndex        = t_index
            break
    search_bit_field = 0
    for t_index in range (startIndex, endIndex+1):
        search_bit_field = search_bit_field | transitions[song][t_index]["tubes"]
    for t_index in range(endIndex+1, len(transitions[song])):
        if inTube(search_bit_field, t_index):
            if tubeExclusive.get() == 0 or transitions[song][t_index]["tubes"] == tube_bit_field:
                selEndTime = transitions[song][t_index]["time"]
                selEndTimeVar.set(displayTime(selEndTime))
                break
    scalePercentage.set("")
    scaleTime.set("")
    for t_index in range(len(transitions[song])):
        if transitions[song][t_index]["selection"] == 1:
            scalePercentage.set("100")
            scaleTime.set(displayTime(int(selEndTime - selStartTime)))
            break


def clearSelection():
    global trans_sel_value, transitions, song, selectionStart, selectionEnd

    for col in range(NUM_COL):
        trans_sel_value[col].set(0)
    for t_index in range(len(transitions[song])):
        transitions[song][t_index]["selection"] = 0
    selectionStart.delete(0, END)
    selStartTimeVar.set("")
    selectionEnd.delete(0, END)
    selEndTimeVar.set("")
    scalePercentage.set("")
    scaleTime.set("")



def copyTrans():
    global trans_sel_value, transitions, song, selectionStart, selectionEnd, copyRepeat, transition, currentTransition

    copyList          = []
    startIndex        = int(selectionStart.get())
    endIndex          = int(selectionEnd.get())
    repeat            = int(copyRepeat.get())
    workingTransitions = []
    timeRefIndex      = 0


    print "Start : ", startIndex
    print "End   : ", endIndex


    for t_index in range(startIndex, endIndex+1, +1):
        if tubeExclusive.get() == 0 and inTube(tube_bit_field, t_index):
            copyList.append(t_index)
        elif tubeExclusive.get() == 1 and transitions[song][t_index]["tubes"] == tube_bit_field:
            copyList.append(t_index)
    for t_index in range (startIndex-1, 0, -1):
        if tubeExclusive.get() == 0 and inTube(tube_bit_field, t_index):
            timeRefIndex = t_index
            break
        elif tubeExclusive.get() == 1 and transitions[song][t_index]["tubes"] == tube_bit_field:
            timeRefIndex = t_index
            break

    timeDelta = transitions[song][currentTransition]["time"] - transitions[song][timeRefIndex]["time"]
    for j in range(len(copyList)):  # Need to make a copy otherwise copying from later in sequence to earlier in sequence will break
        workingTransitions.append(transitions[song][copyList[j]].copy())
    repeatTimeDelta = transitions[song][copyList[len(copyList)-1]]["time"] - transitions[song][timeRefIndex]["time"]
    totalTimeDelta = repeat * repeatTimeDelta
    for j in range(len(copyList)):
        workingTransitions[j]["time"] += timeDelta
        workingTransitions[j]["selection"] = 0
        currentTransition += 1
        transitions[song].insert(currentTransition, workingTransitions[j].copy())
    for i in range(1, repeat):
        for j in range(len(copyList)):
            workingTransitions[j]["time"] += repeatTimeDelta
            workingTransitions[j]["selection"] = 0
            currentTransition += 1
            transitions[song].insert(currentTransition, workingTransitions[j].copy())
    insertRelativeDelay(currentTransition, totalTimeDelta)
    loadTransitions(currentTransition)

def scaleTrans():
    global trans_sel_value, transitions, song, selectionStart, selectionEnd, copyRepeat, transition, currentTransition

    scaleList          = []
    startIndex         = int(selectionStart.get())
    endIndex           = int(selectionEnd.get())
    workingTransitions = []
    timeRefIndex       = 0
    scaleTimeText = re.sub("[^0-9]", "", scaleTime.get())
    if len(scaleTimeText) == 6:
        scaleTimeDuration = time2Miliseconds(scaleTimeText)
        for t_index in range(startIndex, endIndex+1, +1):
            if tubeExclusive.get() == 0 and inTube(tube_bit_field, t_index):
                scaleList.append(t_index)
            elif tubeExclusive.get() == 1 and transitions[song][t_index]["tubes"] == tube_bit_field:
                scaleList.append(t_index)

        relativeTransList = []
        maxTime = 10000000
        maxTimeTransition = len(transitions[song])-1
        search_bit_field = 0
        for t_index in range (len(scaleList)):
            search_bit_field = search_bit_field | transitions[song][scaleList[t_index]]["tubes"]
        for t_index in range(endIndex+1, len(transitions[song])):
            if inTube(search_bit_field, t_index):
                if tubeExclusive.get() == 0 or transitions[song][t_index]["tubes"] == search_bit_field or transitions[song][t_index]["type"] == "END":
                    preScaleDuration = transitions[song][t_index]["time"] - transitions[song][startIndex]["time"]
                    scaleFactor = float(scaleTimeDuration) / preScaleDuration
                    totalTimeDelta = scaleTimeDuration - preScaleDuration
                    scaleList.append(t_index)
                    break
        for t_index in range(len(scaleList)-1):  # Don't include end point to avoid problems with fractional calculations
            timeDelta = transitions[song][scaleList[t_index]]["time"] - transitions[song][startIndex]["time"]
            transitions[song][scaleList[t_index]]["time"] = transitions[song][startIndex]["time"] + int(timeDelta * scaleFactor + 0.5)
            transitions[song][scaleList[t_index]]["duration"] = int(scaleFactor * transitions[song][scaleList[t_index]]["duration"] + 0.5)
        # Do the last transition differently to get time exact
        transitions[song][scaleList[len(scaleList)-1]]["time"] = scaleTimeDuration + transitions[song][startIndex]["time"]
        insertRelativeDelay(scaleList[len(scaleList)-1], totalTimeDelta)
        for t_index in range(len(scaleList)-1):  # Clean up the transitions that overlap with the following scene
            if (transitions[song][scaleList[t_index]]["time"] + transitions[song][scaleList[t_index]]["duration"]) > transitions[song][scaleList[t_index+1]]["time"]:
                timeDelta = transitions[song][scaleList[t_index]]["time"] + transitions[song][scaleList[t_index]]["duration"] - transitions[song][scaleList[t_index+1]]["time"]
                transitions[song][scaleList[t_index+1]]["time"] += timeDelta
                insertRelativeDelay(scaleList[t_index+1], timeDelta)
        loadTransitions(currentTransition)


def deleteTrans():
    global trans_sel_value, transitions, song, selectionStart, selectionEnd, copyRepeat, transition, currentTransition

    deleteList         = []
    startIndex         = int(selectionStart.get())
    endIndex           = int(selectionEnd.get())
    workingTransitions = []
    timeRefIndex       = 0


    for t_index in range(startIndex, endIndex+1, +1):
        if tubeExclusive.get() == 0 and inTube(tube_bit_field, t_index):
            deleteList.append(t_index)
        elif tubeExclusive.get() == 1 and transitions[song][t_index]["tubes"] == tube_bit_field:
            deleteList.append(t_index)
    for t_index in range (startIndex-1, 0, -1):
        if tubeExclusive.get() == 0 and inTube(tube_bit_field, t_index):
            timeRefIndex = t_index
            break
        elif tubeExclusive.get() == 1 and transitions[song][t_index]["tubes"] == tube_bit_field:
            timeRefIndex = t_index
            break

    timeDelta = transitions[song][timeRefIndex]["time"] - transitions[song][deleteList[len(deleteList)-1]]["time"]
    for j in range(len(deleteList)-1, -1, -1):  # Need to count down from the last towards the first to not affect the indicies with each delete
        del transitions[song][deleteList[j]]
    if currentTransition >= deleteList[0]:
        currentTransition -= len(deleteList)
    insertRelativeDelay(timeRefIndex, timeDelta)
    clearSelection()
    loadTransitions(currentTransition)

def changeSong(songName):
    global song, songLUT, songSelection, currentTransition, transitions

    song = songLUT[songName]
    currentTransition = 0
    clearScene()
    loadTransitions(currentTransition)
    print "Song : [", song, "] ,", songName

def checkMotes():
    global tube_status, status_radio_var, alt_status_radio_var, radio_status

    reset_com_count(BROADCAST_MOTE_MAC)
    for mote in range(len(macIDs)):
        if motes[macIDs[mote]]["ack"]["ComCount"] == 1:
            radio_status[mote] = 1
            status_radio_var[mote].set(1)
            alt_status_radio_var[mote].set(1)
        else:
            radio_status[mote] = 0
            status_radio_var[mote].set(0)
            alt_status_radio_var[mote].set(0)


def ChangeMusicTime(*args):
    global musicTime, musicStartTime

    musicTimeText = re.sub("[^0-9]", "", musicTime.get())
    if len(musicTimeText) == 6:
        musicStartTime = time2Miliseconds(musicTimeText)
        musicTime.set(displayTime(musicStartTime))

def ChangeScaleTime(*args):
    global scaleTime, scalePercentage

    scaleTimeText = re.sub("[^0-9]", "", scaleTime.get())
    if len(scaleTimeText) == 6:
        scaleTimeDuration = time2Miliseconds(scaleTimeText)
        scaleTime.set(displayTime(scaleTimeDuration))
        scalePercentage.set(int(100 * scaleTimeDuration / (selEndTime - selStartTime)))

def ChangeScalePercentage(*args):
    global scaleTime, scalePercentage

    scalePercentageText = re.sub("[^0-9]", "", scalePercentage.get())
    if len(scalePercentageText) > 0:
        scaleStartPercentage = int(scalePercentageText)
        scalePercentage.set(scalePercentageText)
        scaleTime.set(displayTime(int(scaleStartPercentage*(selEndTime - selStartTime)/100)))

def PlayMusic():

    global song, musicStartTime, songFileNames, stream, my_thread, is_playing

    concatSong = []
    wavFile = wave.open(os.path.join(os.path.dirname(__file__), "sync_file.wav"),"rb")
    concatSong.append( [wavFile.getparams(), wavFile.readframes(wavFile.getnframes())] )
    wavFile.close()

    wavFile = wave.open(os.path.join(os.path.dirname(__file__), songFileNames[song]),"rb")
    framesize = wavFile.getsampwidth() * wavFile.getnchannels()

    wavFile.setpos(wavFile.tell() + musicStartTime * 441)

    remainingFrames = wavFile.getnframes() - musicStartTime
    concatSong.append( [wavFile.getparams(), wavFile.readframes(remainingFrames)] )
    wavFile.close()

    wavFile = wave.open(os.path.join(os.path.dirname(__file__), "play.wav"), 'wb')
    wavFile.setparams(concatSong[0][0])
    wavFile.writeframes(concatSong[0][1])
    wavFile.writeframes(concatSong[1][1])
    wavFile.close()

    f = wave.open(os.path.join(os.path.dirname(__file__), "play.wav"),"rb")
    #instantiate PyAudio
    p = pyaudio.PyAudio()
    stream = p.open(format = p.get_format_from_width(f.getsampwidth()),
                    channels = f.getnchannels(),
                    rate = f.getframerate(),
                    output = True)
    #read data
    data = f.readframes(CHUNK)

    #play stream
    while data and is_playing:
        stream.write(data)
        data = f.readframes(CHUNK)

    #stop stream
    stream.stop_stream()
    stream.close()

    #close PyAudio
    p.terminate()
    is_playing = False


def playButtonPressed ():
    global is_playing
    global my_thread

    if not is_playing:
        is_playing = True
        my_thread = threading.Thread(target=PlayMusic)
        my_thread.start()



def PlayRight():
    global currTime, playSequence

    if len(playSequence[0]) - currTime > 1:
        currTime += 1
        play_time.set(displayTime(currTime))
        ShowTubes()

def PlayLeft():
    global currTime, playSequence

    if currTime > 0:
        currTime -= 1
        play_time.set(displayTime(currTime))
        ShowTubes()

def Forward10Right():
    global currTime, playSequence

    if len(playSequence[0]) - currTime > 11:
        currTime += 10
        play_time.set(displayTime(currTime))
        ShowTubes()

def Rewind10Left():
    global currTime, playSequence

    if currTime > 9:
        currTime -= 10
        play_time.set(displayTime(currTime))
        ShowTubes()

def Forward100Right():
    global currTime, playSequence

    if len(playSequence[0]) - currTime > 101:
        currTime += 100
        play_time.set(displayTime(currTime))
        ShowTubes()

def Rewind100Left():
    global currTime, playSequence

    if currTime  > 99:
        currTime -= 100
        play_time.set(displayTime(currTime))
        ShowTubes()

def ForwardToEnd():
    global currTime, playSequence

    currTime = len(playSequence[0]) - 1
    play_time.set(displayTime(currTime))
    ShowTubes()

def RewindToStart():
    global currTime, playSequence

    currTime = 0
    play_time.set(displayTime(currTime))
    ShowTubes()


def PlayTime (*args):
    global play_time, currTime

    playTimeText = re.sub("[^0-9]", "", play_time.get())
    if len(playTimeText) == 6:
        currTime = time2Miliseconds(playTimeText)
        play_time.set(displayTime(currTime))
        if len(playSequence) > 1:
            ShowTubes()


def ShowTubes ():
    global playSequence, play_tube

    if currTime in range(len(playSequence[0])):
        for tube in range(NUM_TUBES):
            for pixel in range(NUM_PIXELS):
                color = color2Text(playSequence[tube][currTime][pixel])
                play_tube[tube][pixel].configure(bg=color)
    else:
        print "Time : ", currTime, "not in play sequence time of : ", len(playSequence[0])

def InitPlay ():

    LoadPlay()
    ShowTubes()

def PlaySequence (*args):
    global play_time, currTime

    for time in range(0, len(playSequence[0])-1):
        currTime = time
        ShowTubes()
        sleep(0.01)

def LoadPlay ():
    global extFlash, playSequence, playScenes, currTime, play_time

    # Load Scenes in from ext flash file
    playScenes = []
    extFlash = {}
    if os.path.exists(os.path.join(os.path.dirname(__file__), "scenes.dat")):
        with open("scenes.dat", "r") as textfile:
            for line in textfile:
                add = int(line[0:7])
                data = int(line[8:11])
                extFlash[add] = data
    for sceneIndex in range(32768):
        byteZero = sceneIndex * 128 + 4
        if byteZero in extFlash.keys():
            playScene = []
            for pixel in range(NUM_PIXELS-1, -1, -1):   # Reverse Pixel order so 1 is at the top of the tube
                playPixel = []
                playPixel.append(extFlash[byteZero+(pixel)*4+1])
                playPixel.append(extFlash[byteZero+(pixel)*4+2])
                playPixel.append(extFlash[byteZero+(pixel)*4+3])
                playPixel.append(int(extFlash[byteZero+(pixel)*4]))
                playScene.append(list(playPixel))
            emptyScenes = sceneIndex - len(playScenes)
            if emptyScenes > 0:
                playScenes.extend([None] * emptyScenes)
            playScenes.append(list(playScene))
    # Load Transitions
    playSequence = []
    flicker = []
    currentTube = []
    LED = [0,0,0]
    for pixel in range(NUM_PIXELS):
        currentTube.append(list(LED))
        flicker.append(0)
    for tube in range(NUM_TUBES):
        songFileName = "Mote" + str(tube) + "_song" + str(song) + ".dat"
        if os.path.exists(os.path.join(os.path.dirname(__file__), songFileName)):
            with open(songFileName, "r") as textfile:
                fileBytes = []
                for line in textfile:
                    fileBytes.append(int(line))
        else:
            break
        playTransitions = []
        playTransition = {"type" : "INIT", "stop" : 0, "duration" : 0, "backporch" : 0, "index" : 0}
        bytePtr = 1
        while (not playTransition["type"] == "END"):
            if playTransition["type"] == "INIT":
                playTransition["index"] = fileBytes[bytePtr+1] + (fileBytes[bytePtr+2] << 8)
                playTransitions.append(playTransition.copy())
                playTransition["type"] = trans_type_rev_LUT[fileBytes[bytePtr+3]]
                bytePtr += 4
            elif playTransition["type"] in ["FADE", "SW UP", "SW DN"]:
                playTransition["stop"]      = fileBytes[bytePtr]
                playTransition["index"]     = fileBytes[bytePtr+1] + (fileBytes[bytePtr+2] << 8)
                playTransition["duration"]  = fileBytes[bytePtr+3] + (fileBytes[bytePtr+4] << 8)
                playTransition["backporch"] = fileBytes[bytePtr+5] + (fileBytes[bytePtr+6] << 8)
                playTransitions.append(playTransition.copy())
                playTransition["type"] = trans_type_rev_LUT[fileBytes[bytePtr+7]]
                bytePtr += 8
            if playTransition["type"] == "END":
                playTransition["index"] = 0
                playTransitions.append(playTransition.copy())
        time = 0
        playTube = []
        currentScene = []
        previousScene = []
        for t_index in range(len(playTransitions)):
            if playTransitions[t_index]["type"] == "INIT":
                currentScene = playScenes[playTransitions[t_index]["index"]]
                for pixel in range(NUM_PIXELS):
                    for comp in range(NUM_COMPS-1):
                        LED[comp] = currentScene[pixel][comp]
                    currentTube[pixel] = copy.deepcopy(LED)
                playTube.append(copy.deepcopy(currentTube))
            elif playTransitions[t_index]["type"] == "FADE":
                previousScene = copy.deepcopy(currentTube)
                currentScene = playScenes[playTransitions[t_index]["index"]]
                for deltaT in range(1, playTransitions[t_index]["duration"]+1):
                    for pixel in range(NUM_PIXELS):
                        for comp in range(NUM_COMPS-1):
                            LED[comp] = previousScene[pixel][comp] + int((currentScene[pixel][comp]- previousScene[pixel][comp])*deltaT/playTransitions[t_index]["duration"])
                        currentTube[pixel] = copy.deepcopy(LED)
                    playTube.append(copy.deepcopy(currentTube))
                    time += 1
                for deltaT in range(1, playTransitions[t_index]["backporch"]+1):
                    for pixel in range(NUM_PIXELS):
                        if deltaT % 25 == 0:
                            flicker[pixel] = (randint(0, playScenes[playTransitions[t_index]["index"]][pixel][FLICKER]))
                        for comp in range(NUM_COMPS-1):
                            LED[comp] = int(currentScene[pixel][comp] * (255 - flicker[pixel]) / 255)
                        currentTube[pixel] = copy.deepcopy(LED)
                    playTube.append(copy.deepcopy(currentTube))
                    time += 1
            elif playTransitions[t_index]["type"] == "SW UP":
                if playTransitions[t_index]["stop"] > 30:
                    start = True
                    startStop = playTransitions[t_index]["stop"] - 128
                else:
                    startStop = playTransitions[t_index]["stop"]
                    start = False
                previousScene = copy.deepcopy(currentTube)
                currentScene = playScenes[playTransitions[t_index]["index"]]
                if start == False:
                    pixelDelta = float(31-startStop) / playTransitions[t_index]["duration"]
                    pixelPosAcc = float(30)
                    for deltaT in range(1, playTransitions[t_index]["duration"]+1):
                        pixelPosAcc -= pixelDelta
                        pixelPosWhole = int(pixelPosAcc)
                        fracPos = pixelPosAcc - pixelPosWhole
                        if pixelPosWhole < 0:
                            pixelPosWhole = 0
                        for pixel in range(NUM_PIXELS-1, pixelPosWhole-1, -1):
                            for comp in range(NUM_COMPS-1):
                                LED[comp] = copy.deepcopy(currentScene[pixel][comp])
                            currentTube[pixel] = copy.deepcopy(LED)
                        for comp in range(NUM_COMPS-1):
                            LED[comp] = previousScene[pixel][comp] + int((currentScene[pixel][comp]- previousScene[pixel][comp])*(1-fracPos))
                            currentTube[pixel] = copy.deepcopy(LED)
                        for pixel in range(pixelPosWhole-2, -1, -1):
                            for comp in range(NUM_COMPS-1):
                                LED[comp] = copy.deepcopy(previousScene[pixel][comp])
                            currentTube[pixel] = copy.deepcopy(LED)
                        playTube.append(copy.deepcopy(currentTube))
                        time += 1
                else:
                    pixelDelta = float(31-startStop) / playTransitions[t_index]["duration"]
                    pixelPosAcc = float(startStop)
                    for deltaT in range(1, playTransitions[t_index]["duration"]+1):
                        pixelPosAcc += pixelDelta
                        pixelPosWhole = int(pixelPosAcc)
                        fracPos = pixelPosAcc - pixelPosWhole
                        if pixelPosWhole < 0:
                            pixelPosWhole = 0
                        for pixel in range(NUM_PIXELS-1, pixelPosWhole-1, -1):
                            for comp in range(NUM_COMPS-1):
                                LED[comp] = copy.deepcopy(currentScene[pixel][comp])
                            currentTube[pixel] = copy.deepcopy(LED)
                        pixel = pixelPosWhole
                        for comp in range(NUM_COMPS-1):
                            LED[comp] = previousScene[pixel][comp] + int((currentScene[pixel][comp]- previousScene[pixel][comp])*(1-fracPos))
                        currentTube.append(list(LED))
                        for pixel in range(pixelPosWhole-2, -1, -1):
                            for comp in range(NUM_COMPS-1):
                                LED[comp] = copy.deepcopy(previousScene[pixel][comp])
                            currentTube[pixel] = copy.deepcopy(LED)
                        playTube.append(copy.deepcopy(currentTube))
                        time += 1
                for deltaT in range(1, playTransitions[t_index]["backporch"]+1):
                    for pixel in range(NUM_PIXELS):
                        for comp in range(NUM_COMPS-1):
                            LED[comp] = copy.deepcopy(currentScene[pixel][comp])
                        currentTube[pixel] = copy.deepcopy(LED)
                    playTube.append(copy.deepcopy(currentTube))
                    time += 1
            elif playTransitions[t_index]["type"] == "SW DN":
                if playTransitions[t_index]["stop"] > 30:
                    start = True
                    startStop = playTransitions[t_index]["stop"] - 128
                else:
                    startStop = playTransitions[t_index]["stop"]
                    start = False
                previousScene = copy.deepcopy(currentTube)
                currentScene = playScenes[playTransitions[t_index]["index"]]
                if start == False:
                    pixelDelta = float(startStop) / playTransitions[t_index]["duration"]
                    pixelPosAcc = float(0)
                    for deltaT in range(1, playTransitions[t_index]["duration"]+1):
                        pixelPosAcc += pixelDelta
                        pixelPosWhole = int(pixelPosAcc)
                        fracPos = pixelPosAcc - pixelPosWhole
                        if pixelPosWhole > 30:
                            pixelPosWhole = 30
                        for pixel in range(pixelPosWhole):
                            for comp in range(NUM_COMPS-1):
                                LED[comp] = copy.deepcopy(currentScene[pixel][comp])
                            currentTube[pixel] = copy.deepcopy(LED)
                        if pixelPosWhole < NUM_PIXELS:
                            pixel = pixelPosWhole
                            for comp in range(NUM_COMPS-1):
                                LED[comp] = previousScene[pixel][comp] + int((currentScene[pixel][comp]- previousScene[pixel][comp])*fracPos)
                        currentTube[pixel] = copy.deepcopy(LED)
                        for pixel in range(pixelPosWhole+1, NUM_PIXELS):
                            for comp in range(NUM_COMPS-1):
                                LED[comp] = copy.deepcopy(previousScene[pixel][comp])
                            currentTube[pixel] = copy.deepcopy(LED)
                        playTube.append(copy.deepcopy(currentTube))
                        time += 1
                else:
                    pixelDelta = float(startStop) / playTransitions[t_index]["duration"]
                    pixelPosAcc = float(startStop)
                    for deltaT in range(1, playTransitions[t_index]["duration"]+1):
                        pixelPosAcc += pixelDelta
                        pixelPosWhole = int(pixelPosAcc)
                        fracPos = pixelPosAcc - pixelPosWhole
                        if pixelPosWhole < 0:
                            pixelPosWhole = 0
                        for pixel in range(NUM_PIXELS-1, pixelPosWhole-1, -1):
                            for comp in range(NUM_COMPS-1):
                                LED[comp] = copy.deepcopy(currentScene[pixel][comp])
                            currentTube[pixel] = copy.deepcopy(LED)
                        if pixelPosWhole > 0:
                            for comp in range(NUM_COMPS-1):
                                LED[comp] = previousScene[pixel][comp] + int((currentScene[pixel][comp]- previousScene[pixel][comp])*fracPos)
                            currentTube[pixel] = copy.deepcopy(LED)
                        for pixel in range(pixelPosWhole-2, -1, -1):
                            for comp in range(NUM_COMPS-1):
                                LED[comp] = copy.deepcopy(previousScene[pixel][comp])
                            currentTube[pixel] = copy.deepcopy(LED)
                        playTube.append(copy.deepcopy(currentTube))
                        time += 1
                for deltaT in range(1, playTransitions[t_index]["backporch"]+1):
                    for pixel in range(NUM_PIXELS):
                        for comp in range(NUM_COMPS-1):
                            LED[comp] = copy.deepcopy(currentScene[pixel][comp])
                        currentTube[pixel] = copy.deepcopy(LED)
                    playTube.append(copy.deepcopy(currentTube))
                    time += 1
            elif playTransitions[t_index]["type"] == "END":
                currentScene = playScenes[0]
                for pixel in range(NUM_PIXELS):
                    for comp in range(NUM_COMPS-1):
                        LED[comp] = copy.deepcopy(currentScene[pixel][comp])
                    currentTube[pixel] = copy.deepcopy(LED)
                playTube.append(copy.deepcopy(currentTube))
        playSequence.append(list(playTube))


def main():
    global root, canvas, menu_frame, mode_frame, info_frame
    global vscrollbar
    global util_frame, bsp
    global uart_timeout_list
    global scenes_index
    global scene_flicker
    global scenes_select
    global scenes_tubes
    global active_tubes
    global active_tube_value
    global selectionStart
    global selectionEnd
    global selectionStart
    global selectionEnd
    global trans_sel, trans_sel_value, trans_num, trans_time, trans_type, trans_stop, trans_duration, trans_index, trans_scene, trans_pixels, trans_flicker, pixel_blank, pixel_color
    global trans_tube, trans_radio_var, trans_time_entry, tubeExclusive, copyRepeat, transition_stop
    global pixel_select, flickerScale
    global displayColor
    global palette_sel
    global palette_img
    global palette_tk_img
    global palette_pixels
    global palette_color
    global redScale
    global greenScale
    global blueScale
    global pixels
    global pixel_tk_img
    global pixel_img
    global songSelection
    global songSelValue
    global songNames
    global currentTransition
    # VManager Globals
    global mgrhost, macaddr, voyager, srcPort, config
    global tube_status, status_radio_var, alt_status_radio_var, mote_assign
    global develop
    global musicTime, musicTimeEntry, musicStartTime
    global selStartTimeVar, selEndTimeVar
    global scaleTime, scalePercentage
    global play_tube, play_time
    global radio_status
    global trans_speed
    global scenes_speed, speedVal


    initReset()
    LoadPlay ()
    root = tk.Tk()
    root.geometry("1600x1050")
    root.rowconfigure(2, weight=1)
    root.columnconfigure(0, weight=1)

    root.title('Light Tubes Scene Generator')

    #-- Create the menu frame, and add menus to the menu frame
    menu_frame = tk.Frame(root)
    menu_frame.grid(row=0, column=0, sticky=tk.W+tk.N)
    menu_frame.tk_menuBar(file_menu(), edit_menu(), view_menu(), help_menu())

    ''' UTILITY SCREEN '''
    util_frame = tk.Frame(root)
    util_frame.grid(row=1, column=0, sticky=tk.W+tk.N)
    '''  TUBE ASSIGNMENT '''
    Button(util_frame, text="Check", width=4, command=checkMotes).grid(row=0, column=0, padx=0)
    Label(util_frame, text="Assignment", width=8,  background="white").grid(row=0, column=1)
    alt_tube_status = []
    alt_status_radio_var = []
    mote_assign = []
    for mote in range(NUM_MOTES):
        temp = tk.StringVar()
        alt_status_radio_var.append(temp)
        alt_tube_status.append(Radiobutton(util_frame, text=str(mote+1), variable=alt_status_radio_var[mote], value=1))
        alt_tube_status[mote].grid(row=mote+1, column=0, padx=0, pady=1)
        alt_status_radio_var[mote].set(0)
        mote_assign.append(Pmw.ComboBox(util_frame, entry_width = 4, label_text = " ", labelpos = 'w', selectioncommand = None, scrolledlist_items = moteSelect))
        mote_assign[mote].grid(row=mote+1, column=1, padx=0, columnspan=1)
        if (mote < 12):
            mote_assign[mote].selectitem(mote+1, setentry=1)
        else:
            mote_assign[mote].selectitem(0, setentry=1)
    if develop == 1:
        mote_assign[13].selectitem(1, setentry=1)
        mote_assign[12].selectitem(12, setentry=1)
        mote_assign[0].selectitem(1, setentry=1)
    '''  SIMULATOR OUTPUT '''
    Button(util_frame, text="Load", width=4, command=InitPlay).grid(row=0, column=2, padx=0)
    play_frame = tk.Frame(util_frame, relief=tk.RAISED, borderwidth=1)
    play_frame.grid(row=1, column=2, sticky=tk.W+tk.N, padx=0, pady=1, rowspan=50)
    Button(play_frame, text="|<",  width=2, command=RewindToStart).grid(row=0, column=0, padx=0)
    Button(play_frame, text="<<<", width=2, command=Rewind100Left).grid(row=0, column=1, padx=0)
    Button(play_frame, text="<<",  width=2, command=Rewind10Left).grid(row=0, column=2, padx=0)
    Button(play_frame, text="<",   width=2, command=PlayLeft).grid(row=0, column=3, padx=0)
    Button(play_frame, text=">",   width=2, command=PlayRight).grid(row=0, column=9, padx=0)
    Button(play_frame, text=">>",  width=2, command=Forward10Right).grid(row=0, column=10, padx=0)
    Button(play_frame, text=">>>", width=2, command=Forward100Right).grid(row=0, column=11, padx=0)
    Button(play_frame, text=">|",  width=2, command=ForwardToEnd).grid(row=0, column=12, padx=0)
    play_time = tk.StringVar()
    play_time.trace('w', functools.partial(PlayTime))
    play_time_entry = Entry(play_frame, textvariable=play_time, width=7)
    play_time_entry.grid(row=0, column=4, padx=0, columnspan=3)
    play_trans = tk.StringVar()
    play_trans = "Trans :  " + str(1)
    Label(play_frame, text=play_trans,   width=6, background="white", anchor="e").grid(row=0, column=7, padx=0, columnspan=2)
    Label(play_frame, text="",   width=2, background="white", anchor="e").grid(row=1, column=0, padx=0, columnspan=2)
    for pixel in range(NUM_PIXELS):
        Label(play_frame, text=pixel+1, width=2,  background="white", anchor="e").grid(row=2+pixel, column=0, padx=0, pady=1)
    play_tube_frame = []
    play_tube = []
    for tube in range(NUM_TUBES):
        play_tube_frame.append(tk.Frame(play_frame, relief=tk.RAISED, borderwidth=2))
        play_tube_frame[tube].grid(row=1, column=1+tube, sticky=tk.W+tk.N, padx=0, pady=1, rowspan=40)
        Label(play_tube_frame[tube], text=tube+1, width=2,  background="white", anchor="e").grid(row=0, column=0, padx=0)
        play_pixels = []
        for pixel in range(NUM_PIXELS):
            play_pixels.append(Label(play_tube_frame[tube], text="", width=2,  background="gray90"))
            play_pixels[pixel].grid(row=1+pixel, column=0, padx=10, pady=1)
        play_tube.append(list(play_pixels))
    play_time.set("00:00.00")

    #-- Create the frame for the function settings and populate the frame with check buttons - set buttons to default values.
    mode_frame = tk.Frame(root)
    mode_frame.grid(row=1, column=0, sticky=tk.W+tk.N)

    #-- Create the info frame and fill with initial contents
    info_frame = tk.Frame(root, borderwidth=0)
    info_frame.grid(row=2, column=0, sticky=W+E+N+S)

    vscrollbar = AutoScrollbar(info_frame)
    vscrollbar.grid(row=0, column=1, sticky=N+S)

    canvas = Canvas(info_frame, 
                    yscrollcommand=vscrollbar.set)
    canvas.grid(row=0, column=0, sticky=N+S+E+W)

    vscrollbar.config(command=canvas.yview)

    # make the canvas expandable
    info_frame.grid_rowconfigure(0, weight=1)
    info_frame.grid_columnconfigure(0, weight=1)

    #-- The arguments for rowconfigure are the row that will expand and contract and the relative weight to other rows that will expand or contract    
    info_frame = Frame(canvas)
    info_frame.rowconfigure(0, weight=1)
    info_frame.columnconfigure(0, weight=1)

    ''' Scene Table '''
    scene_table = tk.Frame(info_frame, relief=tk.RAISED, borderwidth=1)
    scene_table.grid(row=1, column=0, sticky=tk.W+tk.N, padx=0, pady=1)
    Button(scene_table, text="<-", width=1, command=scenesLeft).grid(row=0, column=0, padx=0)
    Button(scene_table, text="->", width=1, command=scenesRight).grid(row=0, column=3, padx=0)
    scenes_index = []
    scenes_select = []
    scenes_tubes = []
    scene_flicker = []
    scenes_speed = []
    for index in range(3):
      if index > 0:
        scene_col = index+1
      else:
        scene_col = index
      scenes_index.append(Entry(scene_table, width=4))
      scenes_index[index].grid(row=1, column=scene_col, padx=0)
      scenes_select.append(Button(scene_table, text="o", width=1, command=functools.partial(setActiveScene, index)))
      scenes_select[index].grid(row=2, column=scene_col, padx=0)
      speed_temp = tk.StringVar()
      scenes_speed.append(speed_temp)
      scenes_speed[index].trace('w', functools.partial(ChangeSpeed, index))
      Entry(scene_table, textvariable=scenes_speed[index], width=4).grid(row=3, column=scene_col, padx=0, columnspan=1)
      scene_pixels =[]
      for pixel in range(NUM_PIXELS):
          scene_pixels.append(Label(scene_table, text="", width=2,  background="gray90"))
          scene_pixels[pixel].grid(row=pixel+4, column=scene_col, padx=0, pady=1)
          selectSceneColorWithArg = functools.partial(selectSceneColor, index, pixel)
          scene_pixels[pixel].bind('<Button-1>', selectSceneColorWithArg)
          if (index == 1):
            scene_flicker.append(Label(scene_table, text=pixel, width=2,  background="gray90"))
            scene_flicker[pixel].grid(row=pixel+4, column=1, padx=0, pady=1)
      scenes_tubes.append(list(scene_pixels))

    ''' Edit Table '''
    edit_table = tk.Frame(info_frame, relief=tk.RAISED, borderwidth=1)
    edit_table.grid(row=1, column=1, sticky=tk.W+tk.N, padx=0, pady=1)
    Button(edit_table, text="Set", width=4, command=SetTubes).grid(row=0, column=0, padx=0)
    Button(edit_table, text="Clear", width=4, command=ClearTubes).grid(row=1, column=0, padx=0)
    active_tubes = []
    active_tube_value = []
    for tube in range(NUM_TUBES):
      active_tube_value.append(tk.IntVar())
      active_tubes.append(Checkbutton(edit_table, text=tube+1, variable=active_tube_value[tube], command=updateActiveTubes, width=4, anchor=tk.W))
      active_tubes[tube].grid(row=tube+2, column=0, padx=0, pady=1)
    Label(edit_table, text="", width=1,  background="white").grid(row=14, column=0)  # Spacer
    tubeExclusive = tk.IntVar()
    Checkbutton(edit_table, text="Ex", variable=tubeExclusive, command=updateActiveTubes, width=4, anchor=tk.W).grid(row=15, column=0, padx=0)
    Label(edit_table, text="", width=1,  background="white").grid(row=16, column=0)  # Spacer
    ''' Copy '''
    copyRow = 17
    Button(edit_table, text="Copy", width=6, command=copyTrans).grid(row=copyRow, column=0, padx=0)
    Label(edit_table, text="Repeat", width=6,  background="white").grid(row=copyRow+1, column=0, padx=0)
    copyRepeat = Entry(edit_table, width=6)
    copyRepeat.grid(row=copyRow+2, column=0, padx=0)
    copyRepeat.insert(10, 1)
    Label(edit_table, text="", width=1,  background="white").grid(row=copyRow+3, column=0)  # Spacer
    ''' Selection '''
    selRow = 0
    Label(edit_table, text="Selection", width=6, background="white").grid(row=copyRow+4, column=0, padx=0)
    selection_table = tk.Frame(edit_table, relief=tk.RAISED, borderwidth=1)
    selection_table.grid(row=copyRow+5, column=0, padx=0, pady=1)
    Label(selection_table, text="Start#", width=6, background="white").grid(row=selRow, column=0, padx=0)
    selectionStart = Entry(selection_table, text="Start", width=6)
    selectionStart.grid(row=selRow+1, column=0, padx=0)
    selStartTimeVar = tk.StringVar()
    Label(selection_table, textvariable = selStartTimeVar, width=6, background="white").grid(row=selRow+2, column=0, padx=0)
    Label(selection_table, text="End #", width=6,  background="white").grid(row=selRow+3, column=0, padx=0)
    selectionEnd = Entry(selection_table, width=6)
    selectionEnd.grid(row=selRow+4, column=0, padx=0)
    selEndTimeVar = tk.StringVar()
    Label(selection_table, textvariable = selEndTimeVar, width=6, background="white").grid(row=selRow+5, column=0, padx=0)
    ''' Delete '''
    deleteRow = copyRow + 8
    Label(edit_table, text="", width=1,  background="white").grid(row=copyRow+7, column=0)  # Spacer
    Button(edit_table, text="Delete", width=4, command=deleteTrans).grid(row=deleteRow, column=0, padx=0)
    Label(edit_table, text="", width=1,  background="white").grid(row=copyRow+9, column=0)  # Spacer
    ''' Scale '''
    scaleRow = 0
    Button(edit_table, text="Scale", width=6, command=scaleTrans).grid(row=copyRow+10, column=0, padx=0)
    scale_table = tk.Frame(edit_table, relief=tk.RAISED, borderwidth=1)
    scale_table.grid(row=copyRow+11, column=0, padx=0, pady=1)
    Label(scale_table, text="%", width=6, background="white").grid(row=scaleRow, column=0, padx=0)
    scalePercentage = tk.StringVar()
    scalePercentage.trace('w', ChangeScalePercentage)
    scalePercentageEntry = Entry(scale_table, textvariable=scalePercentage, width=6)
    scalePercentageEntry.grid(row=scaleRow+1, column=0, padx=0)
    Label(scale_table, text="Time", width=6,  background="white").grid(row=scaleRow+2, column=0, padx=0)
    scaleTime = tk.StringVar()
    scaleTime.trace('w', ChangeScaleTime)
    scaleTimeEntry = Entry(scale_table, textvariable=scaleTime, width=6)
    scaleTimeEntry.grid(row=scaleRow+3, column=0, padx=0)

    ''' Transition Table '''
    trans_table = tk.Frame(info_frame, relief=tk.RAISED, borderwidth=1)
    trans_table.grid(row=1, column=3, sticky=tk.W+tk.N, padx=0, pady=1)
    Button(trans_table, text="|<",      width=1, command=goToStartofTrans).grid(row=0, column=1, padx=0)
    Button(trans_table, text="<<",      width=1, command=ffTransLeft).grid(row=0, column=2, padx=0)
    Button(trans_table, text="<-",      width=1, command=transLeft).grid(row=0, column=3, padx=0)
    songSelection = Pmw.ComboBox(trans_table, entry_width = 5, label_text = "", labelpos = 'w', selectioncommand = changeSong, scrolledlist_items = songNames)
    songSelection.grid(row=0, column=6, padx=0, columnspan=2)
    songSelection.selectitem(songNames[0], setentry=1)
    Button(trans_table, text="Clear Sel", width=6, command=clearSelection).grid(row=0, column=9, padx=0)
    Button(trans_table, text="->",        width=1, command=transRight).grid(row=0, column=2*ACTIVE_COL-1, padx=0)
    Button(trans_table, text=">>",      width=1, command=ffTransRight).grid(row=0, column=2*ACTIVE_COL+5, padx=0)
    Button(trans_table, text="Fill",    width=2, command=fillScene).grid(row=0, column=2*ACTIVE_COL+2, padx=0)
    Button(trans_table, text="Clr",     width=2, command=clearScene).grid(row=1, column=2*ACTIVE_COL+2, padx=0)
    Button(trans_table, text="Add",     width=2, command=addTransition).grid(row=0, column=2*ACTIVE_COL+3, padx=0)
    Button(trans_table, text=">|",      width=1, command=goToEndofTrans).grid(row=0, column=2*ACTIVE_COL+6, padx=0)
    Label(trans_table, text="Select",   width=6, background="white", anchor="e").grid(row=1, column=0, padx=0)
    Label(trans_table, text="Tran #",   width=6, background="white", anchor="e").grid(row=2, column=0, padx=0)
    Label(trans_table, text="Time",     width=6, background="white", anchor="e").grid(row=3, column=0, padx=0)
    Label(trans_table, text="Type",     width=6, background="white", anchor="e").grid(row=4, column=0, padx=0)
    Label(trans_table, text="Stop",     width=6, background="white", anchor="e").grid(row=5, column=0, padx=0)
    Label(trans_table, text="Trans",    width=6, background="white", anchor="e").grid(row=6, column=0, padx=0)
    Label(trans_table, text="Scene",    width=6, background="white", anchor="e").grid(row=7, column=0, padx=0)
    for pixel in range(30):
      Label(trans_table, text=pixel+1, width=6,  background="white", anchor="e").grid(row=9+pixel, column=0, padx=0)
    ''' Transitions '''
    trans_sel = []
    trans_sel_value = []
    trans_num = []
    trans_time = []
    trans_type = []
    trans_stop = []
    trans_duration = []
    trans_index = []
    trans_scene = []
    trans_flicker = []
    pixel_select = []
    pixels = []
    pixel_color = []
    pixel_tk_img = []
    pixel_img = []
    pixel_blank = []
    trans_tube = []
    scene_tube = []
    trans_radio_var = []
    trans_time_entry = []
    trans_speed = []
    for col in range (NUM_COL):
      if col > ACTIVE_COL:
        trans_col = 2*col+3
      else:
        trans_col = 2*col+1
      if col == ACTIVE_COL:
        col_span = 4
      else:
        col_span = 2
      trans_sel_value.append(tk.IntVar())
      trans_sel.append(Checkbutton(trans_table, text="", variable=trans_sel_value[col], command=functools.partial(updateSelection, col), width=7, anchor=tk.CENTER))
      if not col == ACTIVE_COL:
          trans_sel[col].grid(row=1, column=trans_col, padx=0, pady=0, columnspan=col_span)
      trans_num.append(Entry(trans_table, width=7))
      trans_num[col].grid(row=2, column=trans_col, padx=0, columnspan=col_span)
      time_temp = tk.StringVar()
      trans_time.append(time_temp)
      trans_time[col].trace('w', functools.partial(ChangeTime, col))
      trans_time_entry.append(Entry(trans_table, textvariable=trans_time[col], width=7))
      trans_time_entry[col].grid(row=3, column=trans_col, padx=0, columnspan=col_span)
      trans_type.append(Pmw.ComboBox(trans_table, entry_width = 5, label_text = " ", labelpos = 'w', selectioncommand = functools.partial(ChangeType, col), scrolledlist_items = transition_type))
      trans_type[col].grid(row=4, column=trans_col, padx=0, columnspan=col_span)
      trans_stop.append(Pmw.ComboBox(trans_table, entry_width = 5, label_text = " ", labelpos = 'w', selectioncommand = functools.partial(ChangeStop, col), scrolledlist_items = transition_stop))
      trans_stop[col].grid(row=5, column=trans_col, padx=0, columnspan=col_span)
      duration_temp = tk.StringVar()
      trans_duration.append(duration_temp)
      trans_duration[col].trace('w', functools.partial(ChangeTransitionTime, col))
      Entry(trans_table, textvariable=trans_duration[col], width=7).grid(row=6, column=trans_col, padx=0, columnspan=col_span)
      scene_temp = tk.StringVar()
      trans_index.append(scene_temp)
      trans_index[col].trace('w', functools.partial(ChangeScene, col))
      Entry(trans_table, textvariable=trans_index[col], width=7).grid(row=7, column=trans_col, padx=0, columnspan=col_span)
      trans_pixels =[]
      scene_tube = []
      scene_radio_var = []
      for pixel in range(NUM_PIXELS):
          if (col == ACTIVE_COL):
            pixel_img.append(Image.new( 'RGB', (20,15), "black"))
            pixels.append(pixel_img[pixel].load())
            for i in range(pixel_img[pixel].size[0]):
                for j in range(pixel_img[pixel].size[1]):
                    pixels[pixel][i,j] = (0, 0, 0)
            pixel_color.append([0, 0, 0, 0])
            pixel_tk_img.append(ImageTk.PhotoImage(pixel_img[pixel]))
            selectPixelColorWithArg = functools.partial(selectPixelColor, pixel)
            pixel_select.append(Button(trans_table, highlightthickness = 0, bd=0))
            pixel_select[pixel].bind('<Button-1>', selectPixelColorWithArg)
            pixel_select[pixel].config(image=pixel_tk_img[pixel])
            pixel_select[pixel].grid(row=pixel+9, column=trans_col+2, padx=0, pady=0)
            revSelectPixelColorWithArg = functools.partial(revSelectPixelColor, pixel)
            pixel_select[pixel].bind('<Button-2>', revSelectPixelColorWithArg)
            trans_flicker.append(Entry(trans_table, font = "Calibri 9", width=2))
            trans_flicker[pixel].grid(row=pixel+9, column=trans_col+1, padx=0, pady=0)
            pixel_blank.append(True)
            Label(trans_table, text=pixel+1, font = "Calibri 10", width=2,  background="white", anchor="e").grid(row=9+pixel, column=trans_col+3, padx=0)
          else:
            trans_pixels.append(Label(trans_table, text="", width=2,  background="gray90"))
            trans_pixels[pixel].grid(row=pixel+9, column=trans_col, padx=0, pady=1)
            if (pixel < NUM_TUBES):
                temp = tk.StringVar()
                scene_radio_var.append(temp)
                ChangeTubeWithArg = functools.partial(ChangeTube, col, pixel)
                scene_tube.append(Radiobutton(trans_table, text="", command = ChangeTubeWithArg, variable=scene_radio_var[pixel], value=1))
                scene_tube[pixel].grid(row=pixel+9, column=trans_col+1, padx=0, pady=1)
                scene_radio_var[pixel].set(1)
      trans_tube.append(list(scene_tube))
      trans_radio_var.append(list(scene_radio_var))
      trans_scene.append(list(trans_pixels))

    ''' Color Selection '''
    control_table = tk.Frame(info_frame, relief=tk.RAISED, borderwidth=1)
    control_table.grid(row=1, column=4, sticky=tk.W+tk.N, padx=0, pady=1)
    color_table = tk.Frame(control_table, relief=tk.RAISED, borderwidth=1)
    color_table.grid(row=0, column=0, sticky=tk.W+tk.N, padx=0, pady=1)
    displayColor = Label(color_table, text="",   width=6, background="gray90")
    displayColor.grid(row=0, column=2, padx=0, columnspan=2)
    redScale = tk.Scale(color_table, from_=0, to=255, orient="vertical", length=200, command=updateRed)
    redScale.grid(row=1, column=1, padx=0)
    Label(color_table, text="R",   width=3, fg = "red", background="white", anchor="e").grid(row=2, column=1, padx=0)
    greenScale = tk.Scale(color_table, from_=0, to=255, orient="vertical", length=200, command=updateGreen)
    greenScale.grid(row=1, column=2, padx=0)
    Label(color_table, text="G",   width=3, fg = "green", background="white", anchor="e").grid(row=2, column=2, padx=0)
    blueScale = tk.Scale(color_table, from_=0, to=255, orient="vertical", length=200, command=updateBlue)
    blueScale.grid(row=1, column=3, padx=0)
    Label(color_table, text="B", width=3, fg = "blue", background="white", anchor="e").grid(row=2, column=3, padx=0)
    flickerScale = tk.Scale(color_table, from_=0, to=100, orient="vertical", length=200)
    flickerScale.grid(row=1, column=4, padx=0)
    Label(color_table, text="F", width=3, fg = "black", background="white", anchor="e").grid(row=2, column=4, padx=0)
    Label(color_table, text="Speed", width=4, fg = "black", background="white", anchor="e").grid(row=3, column=1, padx=0, columnspan=2)
    speedVal = tk.StringVar()
    speedVal.trace('w', ChangeSpeedVal)
    speedEntry = Entry(color_table, textvariable=speedVal, width=4)
    speedEntry.grid(row=3, column=3, padx=0, columnspan=2)

    ''' Color LUT '''
    palette_sel = []
    palette_img = []
    palette_tk_img = []
    palette_pixels = []
    palette_color = []
    for z in range(len(palette_comp_colors)):
        for y in range(len(palette_comp_colors)):
            row_sel = []
            row_img = []
            row_pixels = []
            row_tk_img = []
            palette_row_color = []
            palette_row = z*len(palette_comp_colors) + y
            for palette_col in range(len(palette_comp_colors)):
                row_img.append(Image.new( 'RGB', (PAL_BUTTON_X,PAL_BUTTON_Y), "black"))
                row_pixels.append(row_img[palette_col].load())
                for i in range(row_img[palette_col].size[0]):
                    for j in range(row_img[palette_col].size[1]):
                        row_pixels[palette_col][i,j] = (palette_comp_colors[palette_col], palette_comp_colors[z], palette_comp_colors[y])
                palette_row_color.append((palette_comp_colors[palette_col], palette_comp_colors[z], palette_comp_colors[y]))
                row_tk_img.append(ImageTk.PhotoImage(row_img[palette_col]))
                selectPalleteColorWithArg = functools.partial(selectPalleteColor, palette_row, palette_col)
                row_sel.append(Button(color_table, width = 25, height = 20, highlightthickness = 0, bd=0, command=selectPalleteColorWithArg))
                row_sel[palette_col].config(image=row_tk_img[palette_col])
                row_sel[palette_col].grid(row=palette_row+4, column=palette_col+1, padx=0, pady=0)
            palette_color.append(list(palette_row_color))
            palette_sel.append(list(row_sel))
            palette_img.append(list(row_sel))
            palette_pixels.append(list(row_pixels))
            palette_tk_img.append(list(row_tk_img))
    ''' Music Control '''
    music_table = tk.Frame(control_table, relief=tk.RAISED, borderwidth=1)
    music_table.grid(row=1, column=0, sticky=tk.W+tk.N, padx=0, pady=1)
    Button(music_table, text="Play", width=8, command=playButtonPressed).grid(row=0, column=0, padx=0, columnspan=2)
    Label(music_table, text="Start Time:", width=8, background="white").grid(row=1, column=0, padx=0)
    musicTime = tk.StringVar()
    musicTime.trace('w', ChangeMusicTime)
    musicTimeEntry = Entry(music_table, textvariable=musicTime, width=7)
    musicTimeEntry.grid(row=1, column=1, padx=0)
    Button(music_table, text="Stop", width=8, command=stopSong).grid(row=2, column=0, padx=0, columnspan=2)
    musicStartTime = 0
    musicTime.set("00:00.00")
    ''' Status Table '''
    status_table = tk.Frame(root, relief=tk.RAISED, borderwidth=1)
    status_table.grid(row=0, column=0, padx=0, pady=0)
    Button(status_table, text="Check", width=4, command=checkMotes).grid(row=0, column=0, padx=0)
    tube_status = []
    status_radio_var = []
    radio_status = []
    for mote in range(NUM_MOTES):
        temp2 = tk.StringVar()
        temp2.set(0)
        radio_status.append(0)
        status_radio_var.append(temp2)
        tube_status.append(Radiobutton(status_table, text=str(mote+1), variable=status_radio_var[mote], value=1))
        tube_status[mote].grid(row=0, column=mote+1, padx=0, pady=1)
        status_radio_var[mote].set(0)

    ''' Post GUI Init '''

    loadScenes(0)
    SetTubes()
    currentTransition = 0
    loadTransitions(currentTransition)

    # IO signal configruation table

    canvas.create_window(0, 0, anchor=NW, window=info_frame)
    info_frame.update_idletasks()
    canvas.config(scrollregion=canvas.bbox("all"))

    show_io_config()
    #-- starts the GUI

    #==================== Configure VManager Connection =============
    print '\nConnecting to VManager'
    print 'SmartMesh SDK {0}\n'.format('.'.join([str(i) for i in sdk_version.VERSION]))

    mgrhost = DFLT_VMGR_HOST
    macaddr = TEST_MOTE_MAC
    scrPort = 1

    config = Configuration()
    config.username     = 'dust'
    config.password     = 'dust'
    config.verify_ssl   = False

    if NETWORK_ON:
        # initialize the VManager Python library
        voyager = VManagerApi(host=mgrhost)
        # start listening for data notifications
        voyager.get_notifications('data', notif_callback=process_data)


    root.mainloop()


if __name__=='__main__':
    try:
        main()
    except:
        traceback.print_exc()

