--[[
    a-lurker, copyright, 16 Jan 2015; updated 10 Jan 2016

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License
    version 3 (GPLv3) as published by the Free Software Foundation; 

    In addition to the GPLv3 License, this software is only for private
    or home usage. Commercial utilisation is not authorized.
    
    The above copyright notice and this permission notice shall be included
    in all copies or substantial portions of the Software.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.
]]

local PLUGIN_NAME     = 'EKMmetering'
local PLUGIN_SID      = 'urn:a-lurker-com:serviceId:'..PLUGIN_NAME..'1'
local PLUGIN_VERSION  = '0.51'
local THIS_LUL_DEVICE = nil

local HA_SID           = 'urn:micasaverde-com:serviceId:HaDevice1'
local ENERGY_METER_SID = 'urn:micasaverde-com:serviceId:EnergyMetering1'

local METER_V4 = '4'

local MAIN_REQUEST_V3  = '3'
local MAIN_REQUEST_V4A = '4A'
local MAIN_REQUEST_V4B = '4B'

local IP_PORT   = '50000'
local ipAddress = ''   -- the ATC1000/iSerial IP address

local rxMsgTable = {}

local TASK_ERROR = 2
local m_TaskHandle = -1

-- often used variables
local ONE_MIN_IN_SECS  = 60
local m_MeterModel = ''  -- is set to either: '3' or '4'

-- we can use a secondary meter by setting a value to select the appropriate
-- calculations. The kWh value is loaded into SecondMeterAkWh.
-- '0' = no secondary meter
-- '1' = to grid
-- '2' = from grid
local m_UseSecondMeter = ''

-- we can direct any of the kWh values to Vera's KWH variable:
-- '0' = to grid kWh
-- '1' = from grid kWh
-- '2' = net = from minus to grid kWh
local m_MeteringFunction = ''

local m_PollEnable   = ''  -- set to either: '0' or '1'
local m_PollInterval = ONE_MIN_IN_SECS

 -- these byte arrays should be passed to the functions instead of being global but what the heck
local m_MeterRdRegister = {}
local m_MeterWrRegister = {}
local m_MeterWrData     = {}

-- http://bitop.luajit.org/api.html
local bitFunctions = require('bit')

--[[

READING from and WRITING to EKM meters version 3 & 4:

Baud Rate: 9600 (for v3 & v4 meters) or 1200 (for v2 meters)
RS485, 7 Bit, Even Parity, 1 Stop Bit, No Flow Control.
At 9600 baud that's 0.266 secs per 255 byte message.
The returned data is always 255 bytes, unless it is 0x06 (ACK)

The meter's address is written on each meter. However, 999999999999 (12*9) can be used as a default
address. The default can't be used, if there is more than one meter attached to the RS-485 bus.
The default password is 00000000 (8*0). Best not to change it as there is no factory reset
back to 00000000. A changed password that is "lost or forgotten" would be a problem.

Differences between the meters: The messages are all the same with some minor exceptions:
Version 4 has two main data requests. Version 3 only has one.
Version 4 has additional variables that it can read.
Version 4 has additional variables that it can write.
Version 4 has no TX4_WR_MAX_DEMAND_TIME.

The meter always replies with one of the following:
a) 255 bytes encapsulating the data and always starts with 0x02
b) a single write acknowledge byte equal to 0x06


Sequence for reading:
PC    --> request main data (contains meter address)
Meter <-- main data
PC    --> read specific data request OR end of communication: (01 42 30 03 75)
Meter <-- specific data
PC    --> read more specific data request ... OR end of communication: (01 42 30 03 75)


Sequence for writing:
PC    --> request main data (contains meter address)
Meter <-- main data
PC    --> password
Meter <-- 06
PC    --> write new meter data
Meter <-- 06
PC    --> write more new meter data ... or end of communication: (01 42 30 03 75)

]]

---------------------- start EKM METER MODELS 3 and 4 ------------------------
-- Items with four asterisks **** are in addition to or different from the EKM Version 3 meter
-- Either Request A or Request B will get the meter's attention and is always sent first
-- Version 3 does not use TX_REQUEST_A or TX_REQUEST_B
local TX_REQUEST_START = {0x2F, 0x3F}
local TX_METER_ADDRESS = {0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39}  -- 12 byte meter address; use default: 999999999999
local TX_REQUEST_A     = {0x30, 0x30}  -- ****
local TX_REQUEST_B     = {0x30, 0x31}  -- ****
local TX_REQUEST_END   = {0x21, 0x0D, 0x0A}  -- returns: 02, data, 30 30 21 0D 0A 03, crc16 (255 Bytes total)
--HACK local TX_REQUEST_END   = {0x21, 0x0D, 0x00, 0x0A}  -- returns: 02, data, 30 30 21 0D 0A 03, crc16 (255 Bytes total)
 -- crc16 is not used here


-- Reading from the meter: preamble + command_type + epilogue + crc
-- preamble first
local TX_RD_START                = {0x01, 0x52, 0x31, 0x02, 0x30, 0x30}
-- then the command type
local TX_RD_LAST_MTH_KWH         = {0x31, 0x31}  -- returns: 02 30 30 31 31 28, data bytes, 29 03, crc16 (255 Bytes total)
local TX_RD_LAST_MTH_REV_KWH     = {0x31, 0x32}  -- returns: 02 30 30 31 32 28, data bytes, 29 03, crc16 (255 Bytes total)
local TX_RD_PERIOD_TABLES_1_TO_4 = {0x37, 0x30}  -- returns: 02 30 30 37 30 28, data bytes, 29 03, crc16 (255 Bytes total)
local TX_RD_PERIOD_TABLES_5_TO_8 = {0x37, 0x31}  -- returns: 02 30 30 37 31 28, data bytes, 29 03, crc16 (255 Bytes total)
-- additional variables in Version 4 follow:
local TX_RD_PULSE_INPUT_HISTORY  = {0x31, 0x33}  -- returns: ????  ****
local TX_RD_HOLIDAY_PERIODS      = {0x42, 0x30}  -- returns: ????  ****
--  then the epilogue
local TX_RD_END                  = {0x03}
--  and finally the crc16 of the above, excluding the very first byte 0x01


-- Sending a password
local TX_PASSWORD_START = {0x01, 0x50, 0x31, 0x02, 0x28}
local TX_PASSWORD       = {0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30}  -- 8 byte password: default is 00000000
local TX_PASSWORD_END   = {0x29, 0x03}
--  and finally the crc16 of the above, excluding the very first byte 0x01. crc16 equals 32 44 when password is 00000000


-- Writing to the meter: preamble + command_type + interim + data_for_comand + epilogue + crc
-----------------------
-- preamble first
local TX_WR_START            = {0x01, 0x57, 0x31, 0x02, 0x30, 0x30}
-----------------------
-- then one of these write command types with its associated data
local TX_WR_NEW_ADDRESS      = {0x31, 0x30}  -- 12 bytes new address
local TX_WR_NEW_PASSWORD     = {0x32, 0x30}  --  8 bytes new password; best to leave this alone - lost passwords stay that way
local TX_WR_MAX_DEMAND_CLR   = {0x34, 0x30}  -- 30 30 30 30 30 30
-- this write command not found in Version 4
--local TX4_WR_MAX_DEMAND_TIME  = {0x35, 0x30}  -- **** 1 byte  maximum demand time
local TX_WR_CT_RATIO         = {0x44, 0x30}  --  4 bytes ct ratio
local TX_WR_NEW_TIME         = {0x36, 0x30}  -- 14 bytes new time
local TX_WR_PERIOD_TABLE_1   = {0x37, 0x30}  -- 48 bytes period table 1
local TX_WR_PERIOD_TABLE_2   = {0x37, 0x31}  -- 48 bytes period table 2
local TX_WR_PERIOD_TABLE_3   = {0x37, 0x32}  -- 48 bytes period table 3
local TX_WR_PERIOD_TABLE_4   = {0x37, 0x33}  -- 48 bytes period table 4
local TX_WR_PERIOD_TABLE_5   = {0x37, 0x34}  -- 48 bytes period table 5
local TX_WR_PERIOD_TABLE_6   = {0x37, 0x35}  -- 48 bytes period table 6
local TX_WR_PERIOD_TABLE_7   = {0x37, 0x36}  -- 48 bytes period table 7
local TX_WR_PERIOD_TABLE_8   = {0x37, 0x37}  -- 48 bytes period table 8
local TX_WR_SEASONS_TABLE    = {0x38, 0x30}  -- 48 bytes seasons table
-- additional variables in Version 4 follow:
local TX_WR_HOLIDAY_TABLE    = {0x42, 0x30}  -- **** 80 bytes
local TX_WR_WEEKEND_PERIOD   = {0x43, 0x30}  -- ****  4 bytes
local TX_WR_RELAY_1          = {0x38, 0x31}  -- ****  5 bytes, rly 1 on/off eg 31/30 for 38 37 36 35 (for 8765 seconds) (use 30 30 30 30 for permanent on/off)
local TX_WR_RELAY_2          = {0x38, 0x32}  -- ****  5 bytes, rly 2 on/off eg 31/30 for 38 37 36 35 (for 8765 seconds) (use 30 30 30 30 for permanent on/off)
local TX_WR_PULSE_CONSTANT_1 = {0x41, 0x30}  -- ****  4 bytes
local TX_WR_PULSE_CONSTANT_2 = {0x41, 0x31}  -- ****  4 bytes
local TX_WR_PULSE_CONSTANT_3 = {0x41, 0x32}  -- ****  4 bytes
local TX_WR_BAUD_RATE        = {0x44, 0x31}  -- ****  2 bytes, the internal opto-isolators can limit the usage of higher speeds
local TX_WR_LCD_DISPLAY      = {0x44, 0x32}  -- **** 80 bytes, can chose x amount of 40 values
local TX_WR_ZERO_KWH         = {0x44, 0x33}  -- ****  0 bytes
local TX_WR_IMPULSE_K_KWH    = {0x44, 0x34}  -- ****  4 bytes
local TX_WR_AUTO_MAX_DEMAND  = {0x44, 0x35}  -- ****  1 byte
-----------------------
--  then an interim byte
local TX_WR_INTERIM          = {0x28}
-----------------------
--  @@@ data for the command goes here @@@
-----------------------
--  then the epilogue
local TX_WR_END              = {0x29, 0x03}
--  and finally the crc16 of the above, excluding the very first byte 0x01
-----------------------

-- Send end of communications to meter
local TX_END_OF_COMMS = {0x01, 0x42, 0x30, 0x03, 0x75} -- crc16 is not used here

----------------------- end EKM METER MODELS 3 and 4 -------------------------

--[[
Version 3: here is the layout of the data returned, in response to the main request.
start idx, end idx, variable type, variable name
0,1,2 = decimal places; I = CosTheta, M = map, P = period, S = string, T = time

The version 3 meter gives:
   kWh:          one decimal place
   Voltage:      one decimal place
   Current:      one decimal place
   Watts:       zero decimal places
   Power factor: two decimal places

In most case, the version 4 meter will gives kWh to two decimal places. However, this can change
depending on the CT in use. Everything else has the same number of DPS as the version 3 meter.
]]

local ver3Req = {
--{  1,  1, 'S', 'SOH'},
--{  2,   3, 'N', 'MeterName'},
--{  4,   4, 'N', 'MeterFirmware'},
{  5,  16, 'S', 'MeterAddress'},
{ 17,  24, '1', 'TotalkWh'},        -- abs(forward) + abs(reverse)
{ 25,  32, '1', 'T1kWh'},           -- time periods 1 to 4
{ 33,  40, '1', 'T2kWh'},
{ 41,  48, '1', 'T3kWh'},
{ 49,  56, '1', 'T4kWh'},
{ 57,  64, '1', 'TotalReversekWh'}, -- abs(reverse)
{ 65,  72, '1', 'T1reversekWh'},    -- time periods 1 to 4
{ 73,  80, '1', 'T2reversekWh'},
{ 81,  88, '1', 'T3reversekWh'},
{ 89,  96, '1', 'T4reversekWh'},
{ 97, 100, '1', 'VoltsL1'},
{101, 104, '1', 'VoltsL2'},
{105, 108, '1', 'VoltsL3'},
{109, 113, '1', 'AmpsL1'},
{114, 118, '1', 'AmpsL2'},
{119, 123, '1', 'AmpsL3'},
{124, 130, '0', 'WattsL1'},
{131, 137, '0', 'WattsL2'},
{138, 144, '0', 'WattsL3'},
{145, 151, '0', 'WattsTotal'},
{152, 155, '2', 'CosThetaL1'},      -- 20 31 30 30 = ' 1.00'
{156, 159, '2', 'CosThetaL2'},      -- 20 31 30 30 = ' 1.00'
{160, 163, '2', 'CosThetaL3'},      -- 4C 30 38 33 = 'L0.83' Note the 'L' (inductive), 'C' (capacitive) or ' '  (resistive)
{164, 171, '1', 'MaxDemandWatts'},  -- Demand is the Wattage averaged over the time period specified below. The highest demand is captured until reset.
{172, 172, 'P', 'MaxDemandWattsTimePeriod'},  -- 15 (31h), 30 (32h) or 60 mins (33h)
{173, 186, 'T', 'DateTime'},
{187, 190, '0', 'CTratio'}
--{191, 198, '0', 'PulseCount1'},     -- n/a in ver 3?
--{199, 206, '0', 'PulseCount2'},     -- n/a in ver 3?
--{207, 214, '0', 'PulseCount3'},     -- n/a in ver 3?
--{215, 218, '0', 'PulseRatio1'},     -- n/a in ver 3?
--{219, 222, '0', 'PulseRatio2'},     -- n/a in ver 3?
--{223, 226, '0', 'PulseRatio3'},     -- n/a in ver 3?
--{227, 229, 'M', 'PulseInputHiLo'}   -- n/a in ver 3?
--{230, 247, 'S', 'Reserved'}         -- 18 bytes
--{248, 253, 'S', '30 30 21 0D 0A 03'},
--{254, 254, '0', 'crc16 – LSB AND 07Fh'},
--{255, 255, '0', 'crc16 – MSB AND 07Fh'}
}

-- Version 4: here is the layout of the data returned, in response to the main request A.
-- start idx, end idx, variable type, variable name
local ver4ReqA = {
--{  1,  1, 'S', 'SOH'},
--{  2,   3, 'N', 'MeterName'},
--{  4,   4, 'N', 'MeterFirmware'},
{  5,  16, 'S', 'MeterAddress'},
{ 17,  24, 'D', 'TotalkWh'},        -- abs(forward) + abs(reverse)
{ 25,  32, 'D', 'TotalkVARh'},      -- Volts Amps Reactive
{ 33,  40, 'D', 'TotalReversekWh'}, -- abs(reverse)
{ 41,  48, 'D', 'TotalkWhL1'},
{ 49,  56, 'D', 'TotalkWhL2'},
{ 57,  64, 'D', 'TotalkWhL3'},
{ 65,  72, 'D', 'TotalReversekWhL1'},
{ 73,  80, 'D', 'TotalReversekWhL2'},
{ 81,  88, 'D', 'TotalReversekWhL3'},
{ 89,  96, 'D', 'ResettablekWh'},         -- TX_WR_ZERO_KWH can be used to reset both ResettablekWh
{ 97, 104, 'D', 'ResettableReversekWh'},  -- and ResettableReversekWh as needed
{105, 108, '1', 'VoltsL1'},
{109, 112, '1', 'VoltsL2'},
{113, 116, '1', 'VoltsL3'},
{117, 121, '1', 'AmpsL1'},
{122, 126, '1', 'AmpsL2'},
{127, 131, '1', 'AmpsL3'},
{132, 138, '0', 'WattsL1'},
{139, 145, '0', 'WattsL2'},
{146, 152, '0', 'WattsL3'},
{153, 159, '0', 'WattsTotal'},
{160, 163, 'I', 'CosThetaL1'},
{164, 167, 'I', 'CosThetaL2'},
{168, 171, 'I', 'CosThetaL3'},
{172, 178, '0', 'VARL1'},
{179, 185, '0', 'VARL2'},
{186, 192, '0', 'VARL3'},
{193, 199, '0', 'VARTotal'},
{200, 203, '2', 'Frequency'},
{204, 211, '0', 'PulseCount1'},
{212, 219, '0', 'PulseCount2'},
{220, 227, '0', 'PulseCount3'},
{228, 228, 'M', 'PulseInputHiLo'},        -- see table below
{229, 229, 'M', 'CurrentDirection'},      -- see table below
{230, 230, 'M', 'OutputsOnOffStatus'},    -- see table below
{231, 231, '0', 'DecimalPlaceskWhData'},  -- Typically 2 for V4; depends on the CT; can be: 0,1,2. It's fixed to one dp for V3.
--{232, 233, 'S', 'Reserved'},            -- 2 bytes
{234, 247, 'T', 'DateTime'}
--{248, 253, 'S', '30 30 21 0D 0A 03'},
--{254, 254, '0', 'crc16 – LSB AND 07Fh'},
--{255, 255, '0', 'crc16 – MSB AND 07Fh'}
}

-- array index of DecimalPlaceskWhData in the array ver4ReqA immediately above
DPS_IDX = 37

--[[ all in hex
PulseInputHiLo  CurrentDirection  OutputsOnOffStatus  MaxDemandWattsAutoReset  MaxDemandWattsTimePeriod
1,1,1 = 30	    F,F,F = 31        off / off = 31      off     = 30             15 mins = 31
1,1,0 = 31	    F,F,R = 32        off /  on = 32      monthly = 31             30 mins = 32
1,0,1 = 32	    F,R,F = 33         on / off = 33      weekly  = 32             60 mins = 33
1,0,0 = 33	    R,F,F = 34         on /  on = 34      daily   = 33
0,1,1 = 34	    F,R,R = 35                            hourly  = 34
0,1,0 = 35	    R,F,R = 36
0,0,1 = 36	    R,R,F = 37
0,0,0 = 37	    R,R,R = 38
--]]

-- Version 4: here is the layout of the data returned, in response to the main request B.
-- start idx, end idx, variable type, variable name
local ver4ReqB = {
--{  1,  1, 'S', 'SOH'},
--{  2,   3, 'N', 'MeterName'},
--{  4,   4, 'N', 'MeterFirmware'},
{  5,  16, 'S', 'MeterAddress'},
{ 17,  24, 'D', 'T1kWh'},           -- time periods 1 to 4
{ 25,  32, 'D', 'T2kWh'},
{ 33,  40, 'D', 'T3kWh'},
{ 41,  48, 'D', 'T4kWh'},
{ 49,  56, 'D', 'T1reversekWh'},    -- time periods 1 to 4
{ 57,  64, 'D', 'T2reversekWh'},
{ 65,  72, 'D', 'T3reversekWh'},
{ 73,  80, 'D', 'T4reversekWh'},
{ 81,  84, '1', 'VoltsL1'},
{ 85,  88, '1', 'VoltsL2'},
{ 89,  92, '1', 'VoltsL3'},
{ 93,  97, '1', 'AmpsL1'},
{ 98, 102, '1', 'AmpsL2'},
{103, 107, '1', 'AmpsL3'},
{108, 114, '0', 'WattsL1'},
{115, 121, '0', 'WattsL2'},
{122, 128, '0', 'WattsL3'},
{129, 135, '0', 'WattsTotal'},
{136, 139, 'I', 'CosThetaL1'},      -- 20 31 30 30 = ' 1.00'
{140, 143, 'I', 'CosThetaL2'},      -- 20 31 30 30 = ' 1.00'
{144, 147, 'I', 'CosThetaL3'},      -- 4C 30 38 33 = 'L0.83' Note the 'L' (inductive), 'C' (capacitive) or ' '  (resistive)
{148, 155, '1', 'MaxDemandWatts'},
{156, 156, 'M', 'MaxDemandWattsTimePeriod'},  -- 15 (31h), 30 (32h) or 60 mins (33h) 
{157, 160, '0', 'PulseRatio1'},
{161, 164, '0', 'PulseRatio2'},
{165, 168, '0', 'PulseRatio3'},
{169, 172, '0', 'CTratio'},
{173, 173, 'M', 'MaxDemandWattsAutoReset'},   -- see MaxDemandWattsTimePeriod and table above
{174, 177, '0', 'SettableImpulsesPerkWh'},    -- 2nd pulse o/p: see fig 6 in EKM-Omnimeter-Pulse-v.4-Spec-Sheet.pdf
--{178, 233, 'S', 'Reserved'},                -- 56 bytes
{234, 247, 'T', 'DateTime'}
--{248, 253, 'S', '30 31 21 0D 0A 03'},
--{254, 254, '0', 'crc16 – LSB AND 07Fh'},
--{255, 255, '0', 'crc16 – MSB AND 07Fh'}
}


local modelNames = {
-- latest models; as of Jan 2015:
    {0x10, 0x17, true,  'OmniMeter I v.3'},      -- firmware 13 or 14
    {0x10, 0x22, true,  'OmniMeter II UL v.3'},  -- firmware 14
    {0x10, 0x24, true,  'OmniMeter Pulse v.4'},  -- firmware 15 or 16 and maybe 17 and 18
-- possibly discontinued models:
    {0x10, 0x18, false, '5A25EDS-N'},
    {0x10, 0x16, false, '23EDS-N'},
    {0x10, 0x15, false, '25EDS-N'},
    {0x10, 0x14, false, '15EDS-N'},
    {0x10, 0x13, false, '23EDS-N'},
    {0x10, 0x12, false, '25IDS-N'},
    {0x10, 0x11, false, '15IDS-N'}
}


-- Refer to "CRC info Modbus_over_serial_line_V1_02.pdf"
-- Creating this table: the standard crc16 of the table index is the value for that table entry.
-- This assumes array indicies of 0 to 255. So for example the crc16 for index = 2 is the value = 0xC181
-- Note that Lua indicies start at 1, so we compensate for that in the crc16 code with an increment.
local crcTable = {
  0x0000, 0xC0C1, 0xC181, 0x0140, 0xC301, 0x03C0, 0x0280, 0xC241,
  0xC601, 0x06C0, 0x0780, 0xC741, 0x0500, 0xC5C1, 0xC481, 0x0440,
  0xCC01, 0x0CC0, 0x0D80, 0xCD41, 0x0F00, 0xCFC1, 0xCE81, 0x0E40,
  0x0A00, 0xCAC1, 0xCB81, 0x0B40, 0xC901, 0x09C0, 0x0880, 0xC841,
  0xD801, 0x18C0, 0x1980, 0xD941, 0x1B00, 0xDBC1, 0xDA81, 0x1A40,
  0x1E00, 0xDEC1, 0xDF81, 0x1F40, 0xDD01, 0x1DC0, 0x1C80, 0xDC41,
  0x1400, 0xD4C1, 0xD581, 0x1540, 0xD701, 0x17C0, 0x1680, 0xD641,
  0xD201, 0x12C0, 0x1380, 0xD341, 0x1100, 0xD1C1, 0xD081, 0x1040,
  0xF001, 0x30C0, 0x3180, 0xF141, 0x3300, 0xF3C1, 0xF281, 0x3240,
  0x3600, 0xF6C1, 0xF781, 0x3740, 0xF501, 0x35C0, 0x3480, 0xF441,
  0x3C00, 0xFCC1, 0xFD81, 0x3D40, 0xFF01, 0x3FC0, 0x3E80, 0xFE41,
  0xFA01, 0x3AC0, 0x3B80, 0xFB41, 0x3900, 0xF9C1, 0xF881, 0x3840,
  0x2800, 0xE8C1, 0xE981, 0x2940, 0xEB01, 0x2BC0, 0x2A80, 0xEA41,
  0xEE01, 0x2EC0, 0x2F80, 0xEF41, 0x2D00, 0xEDC1, 0xEC81, 0x2C40,
  0xE401, 0x24C0, 0x2580, 0xE541, 0x2700, 0xE7C1, 0xE681, 0x2640,
  0x2200, 0xE2C1, 0xE381, 0x2340, 0xE101, 0x21C0, 0x2080, 0xE041,
  0xA001, 0x60C0, 0x6180, 0xA141, 0x6300, 0xA3C1, 0xA281, 0x6240,
  0x6600, 0xA6C1, 0xA781, 0x6740, 0xA501, 0x65C0, 0x6480, 0xA441,
  0x6C00, 0xACC1, 0xAD81, 0x6D40, 0xAF01, 0x6FC0, 0x6E80, 0xAE41,
  0xAA01, 0x6AC0, 0x6B80, 0xAB41, 0x6900, 0xA9C1, 0xA881, 0x6840,
  0x7800, 0xB8C1, 0xB981, 0x7940, 0xBB01, 0x7BC0, 0x7A80, 0xBA41,
  0xBE01, 0x7EC0, 0x7F80, 0xBF41, 0x7D00, 0xBDC1, 0xBC81, 0x7C40,
  0xB401, 0x74C0, 0x7580, 0xB541, 0x7700, 0xB7C1, 0xB681, 0x7640,
  0x7200, 0xB2C1, 0xB381, 0x7340, 0xB101, 0x71C0, 0x7080, 0xB041,
  0x5000, 0x90C1, 0x9181, 0x5140, 0x9301, 0x53C0, 0x5280, 0x9241,
  0x9601, 0x56C0, 0x5780, 0x9741, 0x5500, 0x95C1, 0x9481, 0x5440,
  0x9C01, 0x5CC0, 0x5D80, 0x9D41, 0x5F00, 0x9FC1, 0x9E81, 0x5E40,
  0x5A00, 0x9AC1, 0x9B81, 0x5B40, 0x9901, 0x59C0, 0x5880, 0x9841,
  0x8801, 0x48C0, 0x4980, 0x8941, 0x4B00, 0x8BC1, 0x8A81, 0x4A40,
  0x4E00, 0x8EC1, 0x8F81, 0x4F40, 0x8D01, 0x4DC0, 0x4C80, 0x8C41,
  0x4400, 0x84C1, 0x8581, 0x4540, 0x8701, 0x47C0, 0x4680, 0x8641,
  0x8201, 0x42C0, 0x4380, 0x8341, 0x4100, 0x81C1, 0x8081, 0x4040
  }

-- don't change this, it won't do anything. Use the debugEnabled flag instead
local DEBUG_MODE = false

local function debug(textParm, logLevel)
    if DEBUG_MODE then
        local text = ''
        local theType = type(textParm)
        if (theType == 'string') then
            text = textParm
        else
            text = 'type = '..theType..', value = '..tostring(textParm)
        end
        luup.log(PLUGIN_NAME..' debug: '..text,50)

    elseif (logLevel) then
        local text = ''
        if (type(textParm) == 'string') then text = textParm end
        luup.log(PLUGIN_NAME..' debug: '..text, logLevel)
    end
end

-- If non existent, create the variable
-- Update the variable only if needs to be
local function updateVariable(varK, varV, sid, id)
    if (sid == nil) then sid = PLUGIN_SID      end
    if (id  == nil) then  id = THIS_LUL_DEVICE end

    if ((varK == nil) or (varV == nil)) then
        luup.log(PLUGIN_NAME..' debug: '..'Error: updateVariable was supplied with a nil value', 1)
        return
    end

    local newValue = tostring(varV)
    --debug(varK..' = '..newValue)
    debug(newValue..' --> '..varK)

    local currentValue = luup.variable_get(sid, varK, id)
    if ((currentValue ~= newValue) or (currentValue == nil)) then
        luup.variable_set(sid, varK, newValue, id)
    end
end

--[[
-- Test vectors for the crc16 code:
local CRC16TestData1 = {0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09}  -- 1 to 9 in hex   = 0xb20e
local CRC16TestData2 = {0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39}  -- 1 to 9 in ASCII = 0x4b37

-- Checksumming the data and the data's checksum always produces zero:
-- Note the checksum order: lsb, msb: So 0 to 9 in ASCII, then the checksum 0x4b37, all then checksummed, results in 0x0000
local CRC16TestData3 = {0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x37, 0x4b}

-- EKM example: Set period table 5
-- 01 <--- not included in checksum
local CRC16TestData4 =
{0x57, 0x31, 0x02, 0x30, 0x30, 0x37, 0x34, 0x28, 0x30, 0x33, 0x30, 0x30, 0x30, 0x31, 0x30, 0x34,
 0x30, 0x30, 0x30, 0x32, 0x30, 0x37, 0x30, 0x30, 0x30, 0x33, 0x31, 0x31, 0x30, 0x30, 0x30, 0x34,
 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30,
 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x29, 0x03}
]]
-- 67 4C <--- final crc16 checksum and'ed with 0x7f7f (7 bit RS232). Note the lsb, msb order.

-- crc16 polynomial (MODBUS):
-- G(x) = x^16 + x^15 + x^2 + 1 with CRC initialized to 0xFFFF
-- Data values must be bytes, ie 8 active lsb bits. Any higher order bits must be zero.
local function crc16(data, startIdx, endIdx)
    startIdx = startIdx or 1
    endIdx   = endIdx   or #data
    debug('startIdx: '..tostring(startIdx))
    debug('endIdx: '..tostring(endIdx))

    --local crc = 0x0000  -- standard crc16
    local crc = 0xffff  -- MODBUS crc16 is the same as crc16 but the crc is initialised to 0xffff

    -- scan all the incoming data and create the crc
    for byteIdx = startIdx, endIdx do
        -- crc = (crc >> 8) ^ table[(crc ^ ord(ch)) & 0xFF]
        -- break it all up, to make it a bit more readable; although that may slow us down a little
        local rShifted8   = bitFunctions.rshift(crc, 8)
        local readyToMask = bitFunctions.bxor(crc, data[byteIdx])
        local tableKey    = bitFunctions.band(readyToMask, 0xff)
        local tableValue  = crcTable[tableKey+1]  -- Lua tables typically start at 1 not 0

        crc = bitFunctions.bxor(rShifted8, tableValue)
    end

    return crc
end

-- get the standard MODBUS crc16 and modify to suit the EKM meter
local function getEKMcrc(data, startIdx, endIdx)
    local crcResult = crc16(data, startIdx, endIdx)

    -- EKM meter uses 7 bit RS485, so bit 8 = 0
    local EKMcrcMSB = bitFunctions.rshift(crcResult, 8)
    local EKMcrcMSB = bitFunctions.band(EKMcrcMSB, 0x7f)
    local EKMcrcLSB = bitFunctions.band(crcResult, 0x7f)

    debug('crc16: '..tostring(crcResult)..'d, '..string.format('%04X', crcResult)..'h; EKM crc: '..string.format('%02Xh', EKMcrcLSB)..', '..string.format('%02xh', EKMcrcMSB))

    local EKMcrcTable = {EKMcrcLSB, EKMcrcMSB}
    return EKMcrcTable
end

local function verifyCrc(rxMsgTable)
    local crcError = true
    local tabLen = #rxMsgTable
    debug('RX msg buffer size is: '..tostring(tabLen))

    local EKMcrc = getEKMcrc(rxMsgTable, 2, tabLen-2)
    if ((rxMsgTable[tabLen-1] == EKMcrc[1]) and (rxMsgTable[tabLen] == EKMcrc[2])) then
        crcError = false
    end

    return crcError
end

local function encodeMeterTime()
    -- year is only two digits; a weekday is 1-7, not 0-6; also note the required '0' pad
    local nowDate = os.date('%y%m%d') -- year is only two digits
    local nowDofW = tostring(tonumber(os.date('%w'))+1)  -- note: week day is 1-7, not 0-6
    local nowTime = os.date('%H%M%S')
    local nowMT   = table.concat({nowDate, '0', nowDofW, nowTime}) -- note: the '0' pad
    debug('Meter time (wr): '..nowMT)
    return nowMT
end

local function decodeMeterTime()
    -- year is only two digits; a weekday is 1-7, not 0-6; also note the '0' pad in day
    local dateTime = luup.variable_get(PLUGIN_SID, 'DateTime', THIS_LUL_DEVICE) or '00000000000000'                
    local nowMT =
    {
        '20',dateTime:sub(1,2), '/', dateTime:sub(3,4), '/', dateTime:sub(5,6),
        ' day:', dateTime:sub(7,8), ' ', 
        dateTime:sub(9,10), ':', dateTime:sub(11,12), ':', dateTime:sub(13,14)
    }
    debug('Meter time (rd): '..table.concat(nowMT))
    return nowMT
end

local function insertDecimalPoint(str, dps)
    if ((dps < 0) or (dps >= str:len())) then
        debug('dp range failure')
        return ''
    end

    local theNumber = tonumber(table.concat({str:sub(1,-dps-1),'.',str:sub(-dps)}))
    if (theNumber == nil) then
        debug('string does not represent a number')
        return ''
    end

    local strFormat = '%.'..dps..'f'

    return string.format(strFormat, theNumber)
end

local function stringToByteArray(str)
    local result = {}
    for i = 1, str:len() do
        result[i] = str:byte(i)
    end
    return result
end

-- used to display message debug strings
local function byteArrayToHexString(byteArray)
    if (byteArray == nil) then debug ('byteArray is nil in byteArrayToHexString') return '' end

    local str = {}
    for i = 1, #byteArray do
        str[i] = string.format('%02X', byteArray[i])
    end
    return table.concat(str,',')
end

local function byteArrayToString(byteArray)
    if (byteArray == nil) then debug ('byteArray is nil in byteArrayToString') return '' end

    local str = {}
    for i = 1, #byteArray do
        str[i] = string.char(byteArray[i])
    end
    return table.concat(str)
end

local function appendTable(destination, source)
    -- append the source array to the destination array
    for k, v in pairs(source) do
        table.insert(destination,v)
    end
end

-- Assemble a Ver 3 or Ver 4A or Ver 4B main data request message
local function makeMainRequest(request_Type)
    local txMsgTable = {}
    appendTable(txMsgTable, TX_REQUEST_START)

    appendTable(txMsgTable, TX_METER_ADDRESS)

    if (request_Type == MAIN_REQUEST_V4A) then
        appendTable(txMsgTable, TX_REQUEST_A)
    elseif (request_Type == MAIN_REQUEST_V4B) then
        appendTable(txMsgTable, TX_REQUEST_B)
    -- else it's a type 3 request and we don't do anything here
    end

    appendTable(txMsgTable, TX_REQUEST_END)
    -- crc is not needed for this write message
    return txMsgTable
end

-- Assemble a specific data read request message
local function makeSpecificReadRequest(readRegister)
    local txMsgTable = {}
    appendTable(txMsgTable, TX_RD_START)
    appendTable(txMsgTable, readRegister)
    appendTable(txMsgTable, TX_RD_END)
    -- add the crc
    appendTable(txMsgTable, getEKMcrc(txMsgTable, 2))
    return txMsgTable
end

-- Assemble a password send message
local function makePasswordSend()
    local txMsgTable = {}
    appendTable(txMsgTable, TX_PASSWORD_START)
    appendTable(txMsgTable, TX_PASSWORD)
    appendTable(txMsgTable, TX_PASSWORD_END)
    -- add the crc
    appendTable(txMsgTable, getEKMcrc(txMsgTable, 2))
    return txMsgTable
end

-- Assemble a specific data write request message
local function makeSpecificWriteRequest(writeRegister, writeData)
    local txMsgTable = {}
    appendTable(txMsgTable, TX_WR_START)
    appendTable(txMsgTable, writeRegister)
    appendTable(txMsgTable, TX_WR_INTERIM)
    appendTable(txMsgTable, writeData)
    appendTable(txMsgTable, TX_WR_END)
    -- add the crc
    appendTable(txMsgTable, getEKMcrc(txMsgTable, 2))
    return txMsgTable
end

-- extract the variable values out of the returned messages
local function unpackMessage(layoutArray, msgByteArray)

    -- just make sure we have something to work with
    if ((layoutArray == nil) or (msgByteArray == nil)) then
        debug('layoutArray and/or msgByteArray is nil')
        return
    end

    if next(msgByteArray) == nil then
        debug('The received message is empty')
        return
    end

    local timeStamp = os.time()
    updateVariable('LastUpdate', timeStamp, HA_SID)
    updateVariable('KWHReading', timeStamp, ENERGY_METER_SID)

    local timeFormat = '%F %X'
    debug('Last update: '..os.date(timeFormat, timeStamp))
    
    timeFormat = '%H:%M'
    updateVariable('LastUpdateHr', os.date(timeFormat, timeStamp))

    -- find the model: it's stored as two bytes
    local modelFound = false
    local meterName  = "Unknown name"
    for k, v in ipairs(modelNames) do
        modelFound = (v[2] == msgByteArray[3]) and (v[1] == msgByteArray[2])
        if modelFound then
            meterName  = v[4]  -- we've found the name
            modelFound = v[3]  -- but do we have code to handle this model?
            break
        end
    end

    updateVariable('MeterName', meterName)
    debug('MeterName: '..meterName)

    -- don't continue if we can't handle this model
    if (not modelFound) then
        debug('Unknown model name or model not handled: '..meterName)
        return
    end

    -- find the firmware version: it's stored as a byte
    local meterFirmware = string.format('0x%02X', msgByteArray[4])
    updateVariable('MeterFirmware', meterFirmware)
    debug('MeterFirmware: '..meterFirmware)

    -- get the bytes as a string
    local msgString = byteArrayToString(msgByteArray)

    -- Extract the DecimalPlaceskWhData, so we know how many decimal points to use later.
    -- The amount of decimal points only varies for V4 models.
    local dpskWh = '0'
    if (layoutArray == ver4ReqA) then
        -- Note: this value is subsequently written to DecimalPlaceskWhData in the for loop below
        dpskWh = msgString:sub(layoutArray[DPS_IDX][1],layoutArray[DPS_IDX][2])
    else
        -- We need this for when Request B is parsed. It was saved
        -- earlier when the response to Request A was parsed.
        dpskWh = luup.variable_get(PLUGIN_SID, 'DecimalPlaceskWhData', THIS_LUL_DEVICE) or '0'
    end

    -- HACK add in the power consumed by a device on L1, which bypasses the meter, due to a wiring error
    --local correctionValue = 25

    -- update all the variables
    -- 0,1,2 = decimal places; I = CosTheta, M = map, P = period, S = string, T = time
    for k, v in ipairs(layoutArray) do
        local varValue = msgString:sub(v[1],v[2])

        if ((v[3] == 'M') or (v[3] == 'P') or (v[3] == 'S') or (v[3] == 'T')) then
        -- do nothing
        elseif (v[3] == 'D') then  -- for V4 only, the number of decimal points can vary for vars marked with 'D' in the layout array
            varValue = insertDecimalPoint(varValue, tonumber(dpskWh))
        elseif ((v[3] == '0') or (v[3] == '1') or (v[3] == '2')) then  -- the number of decimal points is fixed and determined from the layout array
            varValue = insertDecimalPoint(varValue, tonumber(v[3]))
        elseif (v[3] == 'I') then  -- it's a CosTheta: a 3 digit number to two decimal places with a leading letter of: ' ', 'L', 'C'
            local theNumberPart = insertDecimalPoint(varValue:sub(2,4), 2)
            varValue = varValue:sub(1,1)..theNumberPart
        else
            debug('Unknown type in layout array')
        end

        local varName = v[4]

        -- HACK to fix meter wiring
        --if (varName == 'WattsL1') then varValue = tostring(tonumber(varValue) + correctionValue) end

        updateVariable(varName, varValue)
        debug(varName..': '..varValue)
    end

    -- we duplicate this variable into the ENERGY_METER_SID
    local wattsTotal = luup.variable_get(PLUGIN_SID, 'WattsTotal', THIS_LUL_DEVICE) or '0'
    updateVariable('Watts', wattsTotal, ENERGY_METER_SID)

    -- validate if a secondary meter is in use
	if ((m_UseSecondMeter == '') or (m_UseSecondMeter == nil)) then m_UseSecondMeter = '0' end

    local totalkWh        = tonumber(luup.variable_get(PLUGIN_SID, 'TotalkWh',        THIS_LUL_DEVICE) or 0)
    local totalReversekWh = tonumber(luup.variable_get(PLUGIN_SID, 'TotalReversekWh', THIS_LUL_DEVICE) or 0)

    -- depending on the user's requirements, values from a
    -- secondary meter can be used for the calculations
    if (m_UseSecondMeter == '1') then
        -- a 'to grid' secondary meter is in use
        -- the reverse value comes from that meter
        -- there is no reverse component in the EKM totalkWh measurement
        -- that is: totalkWh = totalForwardkWh
        totalReversekWh = math.abs(tonumber(luup.variable_get(PLUGIN_SID, 'SecondMeterAkWh', THIS_LUL_DEVICE) or 0))
    elseif (m_UseSecondMeter == '2') then
        -- a 'from grid' secondary meter is in use
        -- the forward value comes from that meter
        -- there is no forward component in the EKM totalkWh measurement
        -- that is: totalkWh = totalReversekWh
        totalkWh = totalkWh + math.abs(tonumber(luup.variable_get(PLUGIN_SID, 'SecondMeterAkWh', THIS_LUL_DEVICE) or 0))
    end

    -- if none of the above 'we assume' the EKM meter sees both the forward and reverse values
    -- totalkWh is the total energy recorded, in both the forward and reverse directions
    local totalForwardkWh = totalkWh - totalReversekWh
    local totalNetkWh     = totalForwardkWh - totalReversekWh

    totalForwardkWh = tostring(totalForwardkWh)
    totalReversekWh = tostring(totalReversekWh)
    totalNetkWh     = tostring(totalNetkWh)

    debug('TotalForwardkWh: '..totalForwardkWh)
    debug('TotalReversekWh: '..totalReversekWh)
    debug('TotalNetkWh: '..totalNetkWh)

    updateVariable('TotalForwardkWh', totalForwardkWh)
    updateVariable('TotalNetkWh', totalNetkWh)

    -- depending on the user's requirements, Vera's KWH can be assigned different kWh metering variables
    if ((m_MeteringFunction == '0') or (m_MeteringFunction == '') or (m_MeteringFunction == nil)) then
        -- from grid
        updateVariable('KWH', totalForwardkWh, ENERGY_METER_SID)
    elseif (m_MeteringFunction == '1') then  -- to grid
        updateVariable('KWH', totalReversekWh, ENERGY_METER_SID)
    else -- net = from minus to grid
        updateVariable('KWH', totalNetkWh, ENERGY_METER_SID)
    end

    decodeMeterTime()
end

-- Using the RAW protocol: this function gets called for every RX'ed byte
local function updateMsgBuffer(RXedMsgByte)
    local SOH_CHAR      = 0x01
    local ACK_CHAR      = 0x06
    local RX_MSG_LENGTH = 255

    local bufferFilling = true
    local crcError      = true
    local ackRXed       = false

    -- ACK is a solitary reply to a sent message, so clear the RX buffer
    if (RXedMsgByte == ACK_CHAR) then
        rxMsgTable = {}
        debug('Received ACK')
        ackRXed = true
        return bufferFilling, crcError, ackRXed
    end

    -- SOH signifies the start of a reply, so clear the RX buffer
    if (RXedMsgByte == SOH_CHAR) then
        rxMsgTable = {}
    end

    -- fill the RX message buffer
    table.insert(rxMsgTable, RXedMsgByte)

    -- if the RX buffer is full then validate the checksum
    if (#rxMsgTable == RX_MSG_LENGTH) then
        bufferFilling = false
        debug('Incoming buffer is full: '..byteArrayToHexString(rxMsgTable))
        crcError = verifyCrc(rxMsgTable)
        if (crcError) then
            rxMsgTable = {}
            debug ('Incoming: crc error detected')
        else
            debug ('Incoming: crc is OK')
        end
    end

    -- if the RX buffer has overflowed (somehow), then that's a problem
    if (#rxMsgTable > RX_MSG_LENGTH) then
        bufferFilling = false
        debug('Incoming buffer overflowed: '..byteArrayToHexString(rxMsgTable))
        rxMsgTable = {}
    end

    return bufferFilling, crcError, ackRXed
end

local function sendToMeter(txMsgTable)
    -- If we send a message we can always expect a new reply.
    -- So clear the RX msg buffer, given that expectation.
    rxMsgTable = {}

    if (not luup.io.is_connected(THIS_LUL_DEVICE)) then
        m_TaskHandle = luup.task('No LAN connection to meter', TASK_ERROR, PLUGIN_NAME, m_TaskHandle)
        debug('No LAN connection to meter')
        --luup.set_failure(1,THIS_LUL_DEVICE)
        return false
    end

    local txMsg = byteArrayToString(txMsgTable)
    debug('Sending hex: '..byteArrayToHexString(txMsgTable))
    debug('The hex in ASCII: '..txMsg)

    -- result can be nil, false, or true;  we'll test for true
    local result = luup.io.write(txMsg)
    if (result ~= true) then
        m_TaskHandle = luup.task('Cannot send message - comms error', TASK_ERROR, PLUGIN_NAME, m_TaskHandle)
        debug('Cannot send message - comms error')
        --luup.set_failure(1,THIS_LUL_DEVICE)
        return false
    end

    return true
end

-- COMMS_STATES
local RD_MAIN_DATA                   = 1
local EXPECTING_V4_REQ_A_DATA        = 2
local EXPECTING_V4_REQ_B_DATA        = 3
local EXPECTING_V3_REQ_DATA          = 4

local RD_SPECIFIC_DATA               = 5
local EXPECTING_VX_REQ_DATA_IGNORE_1 = 6
local EXPECTING_SPECIFIC_DATA        = 7

local WR_SPECIFIC_DATA               = 8
local EXPECTING_VX_REQ_DATA_IGNORE_2 = 9
local EXPECTING_PW_ACK               = 10
local EXPECTING_WR_ACK               = 11

local IDLE                           = 12

local COMMS_STATE                    = IDLE

local TRANSACTION_TIMEOUT_INTERVAL_SECS = 5

--[[

     dailyResetCheck()                                                        dailyResetCheck()
     |                                                                        |
-----|----------------------------------60s minimum---------------------------|-

     +-Wr-+
-----|    |--------------------------------------------------------------------

     +------ExChng------+
-----|        5s        |------------------------------------------------------

     +--------------ExChng*2--------------+
-----|                 10s                |------------------------------------

                                          readMeterEKM()
                                          |
------------------------------------------|------------------------------------
                                          +-----Rd-----+
------------------------------------------|            |-----------------------

                                          +------ExChng------+
------------------------------------------|        5s        |-----------------

]]

-- time out target; function needs to be global
function interchangeTimeOut()
    COMMS_STATE = IDLE
end

-- This timer will save the day, if no correct message is RX'ed, in response to a transmission.
-- All msg interchanges must complete within this time period, else they will be cut short.
local function setTxRxInterchangeTimeOut()
    -- all RX TX transactions must be completed within the timing interval
    luup.call_delay('interchangeTimeOut', TRANSACTION_TIMEOUT_INTERVAL_SECS)
end

-- The array of functions to execute for each COMMS_STATE value
local COMM_STATES =
{
--------------------------------------------------------------------------------
-- readMainData
--------------------------------------------------------------------------------
    [RD_MAIN_DATA] =
        function(junk)
            debug('Entered RD_MAIN_DATA')
            setTxRxInterchangeTimeOut()

            local txMsgTable = {}
            if (m_MeterModel == METER_V4) then
                txMsgTable = makeMainRequest(MAIN_REQUEST_V4A)
                COMMS_STATE = EXPECTING_V4_REQ_A_DATA
            else
                txMsgTable = makeMainRequest(MAIN_REQUEST_3)
                COMMS_STATE = EXPECTING_V3_REQ_DATA
            end
            if (not sendToMeter(txMsgTable)) then COMMS_STATE = IDLE end
        end
    ,
    [EXPECTING_V4_REQ_A_DATA] =
        function(RXedMsgByte)
            local bufferFilling, crcError = updateMsgBuffer(RXedMsgByte)
            if bufferFilling then return end
            if crcError then
                COMMS_STATE = IDLE
                return
            end
            unpackMessage(ver4ReqA, rxMsgTable)

            local txMsgTable = makeMainRequest(MAIN_REQUEST_V4B)
            COMMS_STATE = EXPECTING_V4_REQ_B_DATA
            if (not sendToMeter(txMsgTable)) then COMMS_STATE = IDLE end
        end
    ,
    [EXPECTING_V4_REQ_B_DATA] =
        function(RXedMsgByte)
            local bufferFilling, crcError = updateMsgBuffer(RXedMsgByte)
            if bufferFilling then return end
            if (not crcError) then
                unpackMessage(ver4ReqB, rxMsgTable)
            end

            COMMS_STATE = IDLE
            sendToMeter(TX_END_OF_COMMS)
        end
    ,
    [EXPECTING_V3_REQ_DATA] =
        function(RXedMsgByte)
            local bufferFilling, crcError = updateMsgBuffer(RXedMsgByte)
            if bufferFilling then return end
            if (not crcError) then
                unpackMessage(ver3Req, rxMsgTable)
            end

            COMMS_STATE = IDLE
            sendToMeter(TX_END_OF_COMMS)
        end
    ,
--------------------------------------------------------------------------------
--  specificDataRead
--------------------------------------------------------------------------------
    [RD_SPECIFIC_DATA] =
        function(junk)
            debug('Entered RD_SPECIFIC_DATA')
            setTxRxInterchangeTimeOut()

            local txMsgTable = {}
            if (m_MeterModel == METER_V4) then
                txMsgTable = makeMainRequest(MAIN_REQUEST_V4A)
                COMMS_STATE = EXPECTING_VX_REQ_DATA_IGNORE_1
            else
                txMsgTable = makeMainRequest(MAIN_REQUEST_3)
                COMMS_STATE = EXPECTING_VX_REQ_DATA_IGNORE_1
            end
            if (not sendToMeter(txMsgTable)) then COMMS_STATE = IDLE end
        end
    ,
    [EXPECTING_VX_REQ_DATA_IGNORE_1] =
        function(RXedMsgByte)
            local bufferFilling, crcError = updateMsgBuffer(RXedMsgByte)
            if bufferFilling then return end
            if crcError then
                COMMS_STATE = IDLE
                return
            end

            local txMsgTable = makeSpecificReadRequest(m_MeterRdRegister)
            COMMS_STATE = EXPECTING_SPECIFIC_DATA
            if (not sendToMeter(txMsgTable)) then COMMS_STATE = IDLE end
        end
    ,
    [EXPECTING_SPECIFIC_DATA] =
        function(RXedMsgByte)
            local bufferFilling, crcError = updateMsgBuffer(RXedMsgByte)
            if bufferFilling then return end
            if crcError then
                COMMS_STATE = IDLE
                return
            end
            unpackMessage(ver4ReqA, rxMsgTable)

            COMMS_STATE = IDLE
            sendToMeter(TX_END_OF_COMMS)
        end
    ,
--------------------------------------------------------------------------------
-- specificDataWrite
--------------------------------------------------------------------------------
    [WR_SPECIFIC_DATA] =
        function(junk)
            debug('Entered WR_SPECIFIC_DATA')
            setTxRxInterchangeTimeOut()

            local txMsgTable = {}
            if (m_MeterModel == METER_V4) then
                txMsgTable = makeMainRequest(MAIN_REQUEST_V4A)
                COMMS_STATE = EXPECTING_VX_REQ_DATA_IGNORE_2
            else
                txMsgTable = makeMainRequest(MAIN_REQUEST_3)
                COMMS_STATE = EXPECTING_VX_REQ_DATA_IGNORE_2
            end
            if (not sendToMeter(txMsgTable)) then COMMS_STATE = IDLE end
        end
    ,
    [EXPECTING_VX_REQ_DATA_IGNORE_2] =
        function(RXedMsgByte)
            local bufferFilling, crcError = updateMsgBuffer(RXedMsgByte)
            if bufferFilling then return end
            if crcError then
                COMMS_STATE = IDLE
                return
            end
            local txMsgTable = makePasswordSend()
            COMMS_STATE = EXPECTING_PW_ACK
            if (not sendToMeter(txMsgTable)) then COMMS_STATE = IDLE end
        end
    ,
    [EXPECTING_PW_ACK] =
        function(RXedMsgByte)
            local bufferFilling, crcError, ackRXed = updateMsgBuffer(RXedMsgByte)
            if (not ackRXed) then
                COMMS_STATE = IDLE
                return
            end

            local txMsgTable = makeSpecificWriteRequest(m_MeterWrRegister, m_MeterWrData)
            COMMS_STATE = EXPECTING_WR_ACK
            if (not sendToMeter(txMsgTable)) then COMMS_STATE = IDLE end
        end
    ,
    [EXPECTING_WR_ACK] =
        function(RXedMsgByte)
            local bufferFilling, crcError, ackRXed = updateMsgBuffer(RXedMsgByte)
            COMMS_STATE = IDLE
            if (ackRXed) then
                sendToMeter(TX_END_OF_COMMS)
            end
        end
    ,
--------------------------------------------------------------------------------
-- Do stuff all:
--------------------------------------------------------------------------------
    [IDLE] =
        function(RXedMsgChar)
        -- if the comms gets out of whack, then processIncoming()
		-- will (hopefully), dump the junk RXedMsgChar to here
        end
}

-- Using the RAW protocol: this function gets called for every RX'ed byte
-- Function must be local to avoid collisions with "other" processIncoming functions.
-- Such as the L_Arduino.lua
local function processIncoming(RXedMsgChar)
    local RXedMsgByte = RXedMsgChar:byte()

    -- debug('RXedMsgChar: '..RXedMsgChar..' '..string.format('%02X', RXedMsgByte))

    if (COMM_STATES[COMMS_STATE] == nil) then
        debug('COMMS_STATES or its index is invalid: '..COMMS_STATE)
        return
    end
    COMM_STATES[COMMS_STATE](RXedMsgByte)
end

local function dailyResetCheck()
    -- make sure there are no communications already in progress
    if (COMMS_STATE ~= IDLE) then debug('dailyResetCheck NOT IDLE',50) return end

    local nextReset         = luup.sunrise()
    local countersNextReset = luup.variable_get(PLUGIN_SID, 'CountersNextReset', THIS_LUL_DEVICE)

    -- if dawn has just occurred then luup.sunrise() will leap ahead by approx 24 hours
    -- reset the resettable kWh counters in the meter
    countersNextReset = tonumber(countersNextReset)
    if (nextReset > countersNextReset) then
        debug('Dawn occurred: resetting the kWh counters',50)
        m_MeterWrRegister = TX_WR_ZERO_KWH
        m_MeterWrData     = {}

        COMMS_STATE = WR_SPECIFIC_DATA
        COMM_STATES[COMMS_STATE](nil)

        updateVariable('CountersNextReset', tostring(nextReset))
    end
end

-- time out target; function needs to be global
function readMeterEKM()
    -- make sure there are no communications already in progress
    if (COMMS_STATE ~= IDLE) then return end
    debug('Reading meter')

    COMMS_STATE = RD_MAIN_DATA
    COMM_STATES[COMMS_STATE](nil)
end

-- Poll the meter for data
-- time out target; function needs to be global
function pollMeter()
    if (m_PollEnable ~= '1') then return end

    -- at dawn, clear the daily kWh counters
    dailyResetCheck()

    -- delay a bit while (potentially) the reset msg is being sent by dailyResetCheck
    luup.call_delay('readMeterEKM', TRANSACTION_TIMEOUT_INTERVAL_SECS*2)

    -- get the meter info every poll interval
    luup.call_delay('pollMeter', m_PollInterval)
end

-- User service: polling on off
-- function needs to be global
function polling(pollEnable)
    if (not ((pollEnable == '0') or (pollEnable == '1'))) then return end
    m_PollEnable = pollEnable
    updateVariable('PollEnable', m_PollEnable)
end

-- user service: set the metering function: from grid, to grid or net; from-to grid
-- function needs to be global
function setMeteringFunction(meteringFunction)
    if (not ((meteringFunction == '0') or (meteringFunction == '1') or (meteringFunction == '2'))) then return end
    m_MeteringFunction = meteringFunction
    updateVariable('MeteringFunction', m_MeteringFunction)
end

-- User service: set the meter serial number
-- function needs to be global
function setMeterSerialNumber(meterSerialNumber)
    -- serial number must be a 12 digit number (stored as a string)
    meterSerialNumber = meterSerialNumber:match('^(%d%d%d%d%d%d%d%d%d%d%d%d)')
    if (meterSerialNumber:len() ~= 12) then return end
    TX_METER_ADDRESS = stringToByteArray(meterSerialNumber)
    updateVariable('MeterSerialNumber', meterSerialNumber)
end

-- user service: set the metering function: from grid, to grid or net: from minus to grid
-- function needs to be global
function setUseSecondMeter(useSecondMeter)
    if (not ((useSecondMeter == '0') or (useSecondMeter == '1') or (useSecondMeter == '2'))) then return end
    m_UseSecondMeter = useSecondMeter
    updateVariable('UseSecondMeter', useSecondMeter)
end

-- user service: set the meter model
-- function needs to be global
function setMeterModel(meterModel)
    if (not ((meterModel == '3') or (meterModel == '4'))) then return end
    m_MeterModel = meterModel
    updateVariable('MeterModel', m_MeterModel)
end

local function specificDataRead()
    -- NOT IMPLEMENTED;  use the dash software instead
    -- 1) need to turn off polling
    -- 2) ensure any last reads have finished
    -- 3) specify the read register and extract the result
    if (COMMS_STATE == IDLE) then
        -- example
        m_MeterRdRegister = TX_RD_LAST_MTH_KWH

        COMMS_STATE = RD_SPECIFIC_DATA
        COMM_STATES[COMMS_STATE](nil)
    end
end

local function specificDataWrite()
    -- NOT IMPLEMENTED;  use the dash software instead
    -- 1) need to turn off polling
    -- 2) ensure any last reads have finished
    -- 3) specify the write register and write the value byte array
    if (COMMS_STATE == IDLE) then
        -- example
        m_MeterWrRegister = TX_WR_NEW_TIME
        m_MeterWrData     = stringToByteArray(encodeMeterTime())

        COMMS_STATE = WR_SPECIFIC_DATA
        COMM_STATES[COMMS_STATE](nil)
    end
end

-- Start up the plugin
-- Refer to: I_EKMmetering1.xml 
-- <startup>luaStartUp</startup>
-- function needs to be global
function luaStartUp(lul_device)
    THIS_LUL_DEVICE = lul_device
    debug('Initialising plugin: '..PLUGIN_NAME)

    -- Lua ver 5.1 does not have bit functions, whereas ver 5.2 and above do
    debug('Using: '.._VERSION)

    if (bitFunctions == nil) then
        debug('Bit library not found\n')
        return false, 'Bit library not found', PLUGIN_NAME
    end

    -- set up some defaults:
    updateVariable('PluginVersion', PLUGIN_VERSION)

    local debugEnabled = luup.variable_get(PLUGIN_SID, 'DebugEnabled', THIS_LUL_DEVICE)
    if ((debugEnabled == nil) or (debugEnabled == '')) then
	    debugEnabled = '0'
        updateVariable('DebugEnabled', debugEnabled)
    end
	DEBUG_MODE = (debugEnabled == '1')

    local pluginEnabled     = luup.variable_get(PLUGIN_SID,       'PluginEnabled',     THIS_LUL_DEVICE)
    local wholeHouse        = luup.variable_get(ENERGY_METER_SID, 'WholeHouse',        THIS_LUL_DEVICE)
    local actualUsage       = luup.variable_get(ENERGY_METER_SID, 'ActualUsage',       THIS_LUL_DEVICE)
    local watts             = luup.variable_get(ENERGY_METER_SID, 'Watts',             THIS_LUL_DEVICE)
    local kWh               = luup.variable_get(ENERGY_METER_SID, 'KWH',               THIS_LUL_DEVICE)
    local useSecondMeter    = luup.variable_get(PLUGIN_SID,       'UseSecondMeter',    THIS_LUL_DEVICE)
    local secondMeterAkWh   = luup.variable_get(PLUGIN_SID,       'SecondMeterAkWh',   THIS_LUL_DEVICE)
    local meteringFunction  = luup.variable_get(PLUGIN_SID,       'MeteringFunction',  THIS_LUL_DEVICE)
    local pollEnable        = luup.variable_get(PLUGIN_SID,       'PollEnable',        THIS_LUL_DEVICE)
    local pollInterval      = luup.variable_get(PLUGIN_SID,       'PollInterval',      THIS_LUL_DEVICE)
    local countersNextReset = luup.variable_get(PLUGIN_SID,       'CountersNextReset', THIS_LUL_DEVICE)

    if ((pluginEnabled == nil) or (pluginEnabled == '')) then
	    pluginEnabled = '1'
        updateVariable('PluginEnabled', pluginEnabled)
    end

    if ((wholeHouse == nil) or (wholeHouse == '')) then
        -- the readings refer to the whole house, not some individual outlet
        updateVariable('WholeHouse', '1', ENERGY_METER_SID)
    end

    if ((actualUsage == nil) or (actualUsage == '')) then
        -- the readings are actual usage, not estimated usage
        updateVariable('ActualUsage', '1', ENERGY_METER_SID)
    end

    if ((watts == nil) or (watts == '')) then
        -- Watts up?
        updateVariable('Watts', '0', ENERGY_METER_SID)
    end

    if ((kWh == nil) or (kWh == '')) then
        -- no energy recorded so far
        updateVariable('KWH', '0', ENERGY_METER_SID)
    end

    if ((useSecondMeter == nil) or (useSecondMeter == '')) then
        -- set to no secondary meter in use
        setUseSecondMeter('0')
    else
        m_UseSecondMeter = useSecondMeter
    end

    if ((secondMeterAkWh == nil) or (secondMeterAkWh == '')) then
        -- the value "A" in kWh, from a second meter, can be written into this variable
        updateVariable('SecondMeterAkWh', '0')
    end

    if ((meteringFunction == nil) or (meteringFunction == '')) then
        -- for all the climate change deniers, default to supply from the grid only!
        setMeteringFunction('0')
    else
        m_MeteringFunction = meteringFunction
    end

    if ((pollEnable == nil) or (pollEnable == '')) then
        -- turn the polling on
        m_PollEnable = '1'
        polling(m_PollEnable)
    else
        m_PollEnable = pollEnable
    end

    -- don't allow polling any faster than one minute
    local theInterval = tonumber(pollInterval)
    if ((theInterval == nil) or (theInterval < ONE_MIN_IN_SECS)) then
        m_PollInterval = ONE_MIN_IN_SECS
        updateVariable('PollInterval', tostring(ONE_MIN_IN_SECS))
    else
        m_PollInterval = theInterval
    end

    -- the resettable kWh counters are reset at sunrise
    countersNextReset = tonumber(countersNextReset)
    if (countersNextReset == nil) then
        countersNextReset = luup.sunrise()
        updateVariable('CountersNextReset', tostring(countersNextReset))
    end

    local meterModel        = luup.variable_get(PLUGIN_SID, 'MeterModel',        THIS_LUL_DEVICE)
    local meterSerialNumber = luup.variable_get(PLUGIN_SID, 'MeterSerialNumber', THIS_LUL_DEVICE) or ''

    -- The user must enter a meter model number
    if ((meterModel == nil) or (meterModel == '')) then
        -- first time round, this will create the variable but
        -- it remains invalid; the user must set it
        m_MeterModel = ''
        luup.variable_set(PLUGIN_SID, 'MeterModel', m_MeterModel, THIS_LUL_DEVICE)
    else
        m_MeterModel = meterModel
    end

    -- The user must enter a 12 digit meter serial number
    meterSerialNumber = meterSerialNumber:match('^(%d%d%d%d%d%d%d%d%d%d%d%d)')
    if ((meterSerialNumber == nil) or (meterSerialNumber == '') or (meterSerialNumber:len() ~= 12)) then
        -- first time round, this will create the variable but
        -- it remains invalid; the user must set it
        meterSerialNumber = ''
        luup.variable_set(PLUGIN_SID, 'MeterSerialNumber', meterSerialNumber, THIS_LUL_DEVICE)
        -- TX_METER_ADDRESS equals the default address '999999999999' at this point
    else
        TX_METER_ADDRESS = stringToByteArray(meterSerialNumber)
    end

    if ((m_MeterModel == '') or (meterSerialNumber == '')) then
    return false, 'Do a "Reload", then enter the meter model (3 or 4) and the 12 digit SN and "Reload" again.', PLUGIN_NAME
    end

    if (pluginEnabled ~= '1') then return true, 'All OK', PLUGIN_NAME end

    -- set up the ip connection. This plugin will never use direct serial - it's way too inefficient with these meters.
    local ipa = luup.devices[THIS_LUL_DEVICE].ip
    local ipAddress = ipa:match('^(%d%d?%d?%.%d%d?%d?%.%d%d?%d?%.%d%d?%d?)')
    local ipPort    = ipa:match(':(%d+)$')

    if ((ipAddress == nil) or (ipAddress == '')) then
        return false, 'Enter a valid IP address', PLUGIN_NAME
    end

    if (ipPort == nil) then ipPort = IP_PORT end

    debug('Using IP address: '..ipAddress..':'..ipPort)
    luup.io.open(THIS_LUL_DEVICE, ipAddress, ipPort)

    -- delay so that the first poll occurs delay interval after start up
    local INITIAL_POLL_INTERVAL_SECS = 70
    luup.call_delay('pollMeter', INITIAL_POLL_INTERVAL_SECS)

    return true, 'All OK', PLUGIN_NAME
end
