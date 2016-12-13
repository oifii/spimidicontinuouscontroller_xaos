/*
 * Copyright (c) 2010-2016 Stephane Poirier
 *
 * stephane.poirier@oifii.org
 *
 * Stephane Poirier
 * 3532 rue Ste-Famille, #3
 * Montreal, QC, H2X 2L1
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

#include "portmidi.h"
#include "porttime.h"
#include "stdlib.h"
#include "stdio.h"
#include "string.h"
#include "assert.h"
#include "math.h" //i.e. for min() and max() function calls
#include "windows.h" //i.e. for Sleep() function calls

//new parameters
//char global_begin[1024]={"begin.ahk"};
//char global_end[1024]={"end.ahk"};
char global_begin[1024]={""};
char global_end[1024]={""};

#define INPUT_BUFFER_SIZE 100
#define OUTPUT_BUFFER_SIZE 0
#define DRIVER_INFO NULL
#define TIME_PROC ((int32_t (*)(void *)) Pt_Time)
#define TIME_INFO NULL
#define TIME_START Pt_Start(1, 0, 0) /* timer started w/millisecond accuracy */

#define STRING_MAX 80 /* used for console input */

int32_t latency = 0;


/* from oifii.org's autohotkey midi library, but adapted for channel id between 0 and 15
midiOutShortMsg(h_midiout, EventType, Channel, Param1, Param2) 
{ 
  ;h_midiout is handle to midi output device returned by midiOutOpen function 
  ;EventType and Channel are combined to create the MidiStatus byte.  
  ;MidiStatus message table can be found at http://www.midi.org/techspecs/midimessages.php 
  ;Possible values for EventTypes are NoteOn (N1), NoteOff (N0), CC, PolyAT (PA), ChanAT (AT), PChange (PC), Wheel (W) - vals in () are optional shorthand 
  ;SysEx not supported by the midiOutShortMsg call 
  ;Param3 should be 0 for PChange, ChanAT, or Wheel.  When sending Wheel events, put the entire Wheel value 
  ;in Param2 - the function will split it into it's two bytes 
  ;returns 0 if successful, -1 if not.  
  
  ;Calc MidiStatus byte combining a channel number between 0 and 15
  If (EventType = "NoteOn" OR EventType = "N1") 
    MidiStatus :=  144 + Channel 
  Else if (EventType = "NoteOff" OR EventType = "N0") 
    MidiStatus := 128 + Channel 
  Else if (EventType = "NoteOffAll") 
    ;MidiStatus := 124 + Channel
    MidiStatus := 176 + Channel
  Else if (EventType = "CC") 
    MidiStatus := 176 + Channel 
  Else if (EventType = "PolyAT" OR EventType = "PA") 
    MidiStatus := 160 + Channel 
  Else if (EventType = "ChanAT" OR EventType = "AT") 
    MidiStatus := 208 + Channel 
  Else if (EventType = "PChange" OR EventType = "PC") 
    MidiStatus := 192 + Channel 
  Else if (EventType = "Wheel" OR EventType = "W") 
  {  
    MidiStatus := 224 + Channel 
    Param2 := Param1 >> 8 ;MSB of wheel value 
    Param1 := Param1 & 0x00FF ;strip MSB, leave LSB only 
  } 

  ;Midi message Dword is made up of Midi Status in lowest byte, then 1st parameter, then 2nd parameter.  Highest byte is always 0 
  dwMidi := MidiStatus + (Param1 << 8) + (Param2 << 16) 
*/

//caller passes input parameters
//caller allocates output parameters (for this function to compute):
//double fNumEvents = 0; //number of additional events, after first is sent on startdelay
//double fEventDelay = 0;
void compute_number_of_events_and_relative_delay(int ccstart, int ccend, int ccstep, int serieduration_ms, int* pnNumEvents, double* pfEventDelay)
{
    int nNumEvents = *pnNumEvents; //number of additional events, after first is sent on startdelay
    double fEventDelay = *pfEventDelay;
    double fNumEvents = 0; //number of additional events, after first is sent on startdelay
    if(ccstep!=0)
    {
        fNumEvents = abs((ccend - ccstart)/ccstep);
        nNumEvents = (int) ceil(fNumEvents);
        fEventDelay = (serieduration_ms+0.0f)/(nNumEvents+0.0f); 
    }
    else
    {
        //ccstep==0
        if(ccend!=ccstart)
        {
            fNumEvents=1;
            nNumEvents=(int)fNumEvents;
            fEventDelay = serieduration_ms;
        }
        else
        {
            //fNumEvents=0;
            fNumEvents=1; //spi 2014
            nNumEvents=(int)fNumEvents;
            fEventDelay=0;
        }
    }            
	#ifdef DEBUG 
		printf("fNumEvents: %f\n", fNumEvents);
		printf("nNumEvents: %d additional events (aside first event)\n", nNumEvents);
		printf("fEventDelay: %f ms\n", fEventDelay);
	#endif
    *pnNumEvents = nNumEvents; //write to output parameter
    *pfEventDelay = fEventDelay; //write to output parameter
	return;
}


/* midiprogram_stream exercises windows winmm API's stream mode */
/*    The winmm stream mode is used for latency>0, and sends
   timestamped messages. The timestamps are relative (delta) 
   times, whereas PortMidi times are absolute. Since peculiar
   things happen when messages are not always sent in advance,
   this function allows us to exercise the system and test it.
 */
//warning: the use of this timestamped stream of midi messages
//         provoques sending CC 64 value 0 twice to all channels 
//         tested by spi.
#define MAXEVENTS  2000  //somewhat arbitrary, ask CP for typical max number of ccstep to be use in real world musical applications

void midicontinuouscontroller_stream(int latency, int deviceid, int close_mididevice_onexit, int channelid, int ccnumber, int ccstart, int ccend, int ccstep, int startdelay_ms, int serieduration_ms) 
{
	int ccvalue = 0;
	int index=0; 
	int ccnext=0;
	int nNumEvents = 0; 
	double fShouldBeDelay = 0;
	long iRelativeDelay = 0;
	double fEventDelay = 0;
    PmStream* midi;
	char line[80];
    PmEvent buffer[MAXEVENTS];

    /* It is recommended to start timer before PortMidi */
    TIME_START;

	/* open output device */
    Pm_OpenOutput(&midi, 
                  deviceid, 
                  DRIVER_INFO,
                  OUTPUT_BUFFER_SIZE, 
                  TIME_PROC,
                  TIME_INFO, 
                  latency);
	#ifdef DEBUG
		printf("Midi Output opened with %ld ms latency.\n", (long) latency);
	#endif //DEBUG

	//int nNumEvents = 0; 
	//double fEventDelay = 0;
	compute_number_of_events_and_relative_delay(ccstart, ccend, ccstep, serieduration_ms, &nNumEvents, &fEventDelay);

	if(nNumEvents>=(MAXEVENTS-2))
	{
		printf("warning, maximum number of events reached, will have to clip number of cc sent to %d%\n", (MAXEVENTS-2));
		printf("write to stephane.poirier@nakedsoftware.org for demanding an upgrade of this program%\n");
		//if does not abort, will have to clip number of cc sent
		nNumEvents=MAXEVENTS-3;
	}

    ////////////////////////////////////////////////////////
    //send all events delayed by proper thread sleeping time 
    ////////////////////////////////////////////////////////
    //int index=0;
    //int nCC_next=0;
    for(index=0; index<(nNumEvents); index++)
    { 
        ccnext = index*ccstep + ccstart; 
        fShouldBeDelay = fEventDelay * (index+0.0f); // + nStartDelay; 
        iRelativeDelay = (long)(fShouldBeDelay+0.5); //round(fShouldBeDelay);  
 		// writing midi events using timestamps
		if(index==0) 
		{
			buffer[index].timestamp = startdelay_ms;
		}
        else 
		{
			buffer[index].timestamp = iRelativeDelay;
		}
		buffer[index].message = Pm_Message((unsigned char)(176+channelid), (unsigned char)ccnumber, (unsigned char)ccnext);
		//Pm_WriteShort(midi, buffer[0].timestamp, buffer[0].message);
    } 
    //check to see if we still need to send ccEnd value             
    if( (ccstep>0)&&(ccnext<ccend) || (ccstep<0)&&(ccnext>ccend) ) //if (nCC_next < nCC_end) 
    { 
		nNumEvents++; //incrementing nNumEvents so it will now reflect the total of CC sent
		//todo: should index be increased of +1 in here? 
        fShouldBeDelay = fEventDelay * (index+0.0f);// + nStartDelay; 
        iRelativeDelay = (long)(fShouldBeDelay+0.5); //round(fShouldBeDelay);  
        ccnext = ccend;
		// writing midi events using timestamps
		buffer[index].timestamp = iRelativeDelay;
		buffer[index].message = Pm_Message((unsigned char)(176+channelid), (unsigned char)ccnumber, (unsigned char)ccnext);
		//Pm_WriteShort(midi, buffer[0].timestamp, buffer[0].message);
    } 

	//sending midi messages
	Pm_Write(midi, buffer, nNumEvents); //todo: double check if should be +1 or not, nNumEvents has already be incremented hereabove

	if(close_mididevice_onexit==TRUE)
	{
		/* close device (this not explicitly needed in most implementations) */
		Pm_Close(midi);
		Pm_Terminate();
		#ifdef DEBUG
			printf("done closing and terminating...\n");
		#endif //DEBUG
	}
}

//the purpose of creating nostream() version was to attempt to prevent cc 64 values being sent on all channels when closing mididevice
//by relying on Pm_WriteShort to send midi message instead of Pm_Write to send midi event (a midi message with timestamp) but did not
//find a way to send midi message without timestamp other than by specifying zero latency when opening the mididevice which provoques
//timestamps to be ignored later on when sending mesage onto this device and thereby prevents cc 64 value 0 to be sent on all channels
//upon closing mididevice.
void midicontinuouscontroller_nostream(int latency, int deviceid, int close_mididevice_onexit, int channelid, int ccnumber, int ccstart, int ccend, int ccstep, int startdelay_ms, int serieduration_ms) 
{
	int ccvalue = 0;
	int index=0; 
	int ccnext=0;
	int nNumEvents = 0; 
	double fShouldBeDelay = 0;
	long iRelativeDelay = 0;
	double fEventDelay = 0;
    PmStream* midi;
	char line[80];
    PmEvent buffer[3];

    /* It is recommended to start timer before PortMidi */
    TIME_START;

	/* open output device */
    Pm_OpenOutput(&midi, 
                  deviceid, 
                  DRIVER_INFO,
                  OUTPUT_BUFFER_SIZE, 
                  TIME_PROC,
                  TIME_INFO, 
                  latency);
#ifdef DEBUG
    printf("Midi Output opened with %ld ms latency.\n", (long) latency);
#endif //DEBUG

	//int nNumEvents = 0; 
	//double fEventDelay = 0;
	compute_number_of_events_and_relative_delay(ccstart, ccend, ccstep, serieduration_ms, &nNumEvents, &fEventDelay);


    ////////////////////////////////////////////////////////
    //send all events delayed by proper thread sleeping time 
    ////////////////////////////////////////////////////////
    //int index=0;
    //int nCC_next=0;
    for(index=0; index<(nNumEvents); index++)
    { 
        ccnext = index*ccstep + ccstart; 
        //fShouldBeDelay = fEventDelay * (index+0.0f); // + nStartDelay; 
        fShouldBeDelay = fEventDelay; //spi 2014
        iRelativeDelay = (long)(fShouldBeDelay+0.5); //round(fShouldBeDelay);  
        if(index==0) {Sleep((DWORD)startdelay_ms);}
            else {Sleep((DWORD)iRelativeDelay);}
		// writing midi for immediate output, we use timestamps of zero
		buffer[0].timestamp = -1;
		buffer[0].message = Pm_Message((unsigned char)(176+channelid), (unsigned char)ccnumber, (unsigned char)ccnext);
		Pm_WriteShort(midi, buffer[0].timestamp, buffer[0].message);
    } 
    //check to see if we still need to send ccEnd value             
    if( (ccstep>0)&&(ccnext<ccend) || (ccstep<0)&&(ccnext>ccend) ) //if (nCC_next < nCC_end) 
    { 
        //fShouldBeDelay = fEventDelay * (index+0.0f);// + nStartDelay; 
        fShouldBeDelay = fEventDelay; //spi 2014
        iRelativeDelay = (long)(fShouldBeDelay+0.5); //round(fShouldBeDelay);  
        Sleep((DWORD)iRelativeDelay);
        ccnext = ccend;
		//writing midi for immediate output, we use timestamps of zero
		buffer[0].timestamp = -1;
		buffer[0].message = Pm_Message((unsigned char)(176+channelid), (unsigned char)ccnumber, (unsigned char)ccnext);
		Pm_WriteShort(midi, buffer[0].timestamp, buffer[0].message);
    } 

	if(close_mididevice_onexit==TRUE)
	{
		/* close device (this not explicitly needed in most implementations) */
		Pm_Close(midi);
		Pm_Terminate();
		#ifdef DEBUG
			printf("done closing and terminating...\n");
		#endif //DEBUG
	}

}


/* if caller alloc devicename like this: char devicename[STRING_MAX]; 
	then parameters are devicename and STRING_MAX respectively        */
int get_device_id(const char* devicename, int devicename_buffersize)
{
	int deviceid=-1;
	int i;
    for (i=0; i<Pm_CountDevices(); i++) 
	{
        const PmDeviceInfo* info = Pm_GetDeviceInfo(i);
 		if(strcmp(info->name, devicename)==0) 
		{
			deviceid=i;
			break;
		}
    }
	#ifdef DEBUG
		if(deviceid==-1)
		{
			printf("get_device_id(), did not find any matching deviceid\n");
		}
	#endif //DEBUG
	return deviceid;
}


void show_usage()
{
	int i;
    printf("Usage: midicontinuouscontroller [-h] [-l latency-in-ms] [-d <device name>] <channel id> <cc number> <cc start value> <cc end value> <cc step value> <start delay> <serie duration>\n");
	printf("\n"); 
    printf("	<device name> can be one of the following midi output devices:\n");
    for (i=0; i<Pm_CountDevices(); i++) 
	{
        const PmDeviceInfo* info = Pm_GetDeviceInfo(i);
        if (info->output) printf("%d: %s\n", i, info->name);
    }
    //printf("    <channel id>\tmidi channel, integer between 1 and 16");
    printf("    <channel id>\tmidi channel, integer between 0 and 15");
    printf("    <cc number>\tcc number to send to, integer between 0 and 127");
    printf("    <cc start value>\tfirst cc value to send, integer between 0 and 127");  
    printf("    <cc end value>\tlast cc value to send (101 corresponds to 0dB for a SONAR fader with midi remote control)"); 
    printf("    <cc end value>\tincremental value of each successive cc value sent e.g. 2 would mean send out 0, 2, 4, 6, etc."); 
    printf("    <start delay>\tnumber of ms before sending the 2nd event.  The first event is sent immediately to 'initialize the cc"); 
    printf("    <serie duration>\tnumber of ms that the entire series of cc events should take.");                        
	printf("Usage example specifying optional latency and output device, respectively 20ms and \"Out To MIDI Yoke:  1\", along with mandatory channel id and program number\n");
	printf("midicontinuouscontroller -l 20 \"Out To MIDI Yoke:  1\" 1 64 101 1 -5 700 5000\n");
	printf("Usage example not specifying optional latency and output device, in order to use the defaults, along with mandatory parameters\n");
	printf("midicontinuouscontroller 1 64 101 1 -5 700 5000\n");
    exit(0);
}

int main(int argc, char *argv[])
{
    int i = 0, n = 0, id=0;
    char line[STRING_MAX];

	int close_mididevice_onexit = FALSE;
	int latency_valid = FALSE;
    char devicename[STRING_MAX];
	int devicename_valid = FALSE;
	//int channelid = 0;
	int channelid = 1; //default user specified channelid must be between 1 and 16
	int channelid_valid = FALSE;
	int ccnumber = 0;
	int ccnumber_valid = FALSE;
	int ccstart = 0;
	int ccstart_valid = FALSE;
	int ccend = 0;
	int ccend_valid = FALSE;
	int ccstep = 0;
	int ccstep_valid = FALSE;
	int startdelay_ms = 0;
	int startdelay_ms_valid = FALSE;
	int serieduration_ms = 0;
	int serieduration_ms_valid = FALSE;

	int deviceid=-1;
	const PmDeviceInfo* info;

    if(argc==1) show_usage();
    for (i = 1; i < argc; i++) 
	{
        if (strcmp(argv[i], "-h") == 0) 
		{
            show_usage();
        } 
		else if (strcmp(argv[i], "-l") == 0 && (i + 1 < argc)) 
		{
			//optional parameter, latency
            i = i + 1;
            latency = atoi(argv[i]);
            latency_valid = TRUE;
        } 
		else if ( (strcmp(argv[i], "-b") == 0 && (i + 1 < argc)) ||
				  (strlen(argv[i])>2) ) 
		{
			//optional parameter, devicename
			if(strcmp(argv[i], "-b") == 0){ i=i+1;}
            strcpy(global_begin, argv[i]);
            devicename_valid = TRUE;
        } 
		else if ( (strcmp(argv[i], "-e") == 0 && (i + 1 < argc)) ||
				  (strlen(argv[i])>2) ) 
		{
			//optional parameter, devicename
			if(strcmp(argv[i], "-e") == 0){ i=i+1;}
            strcpy(global_end, argv[i]);
            devicename_valid = TRUE;
        } 
		else if ( (strcmp(argv[i], "-d") == 0 && (i + 1 < argc)) ||
				  (strlen(argv[i])>2) ) 
		{
			//optional parameter, devicename
			if(strcmp(argv[i], "-d") == 0){ i=i+1;}
            strcpy(devicename, argv[i]);
            devicename_valid = TRUE;
        } 
		else if (strcmp(argv[i], "-c") == 0) 
		{
			//optional parameter, enabling option to close device every time this program is called
            i = i + 1;
            close_mididevice_onexit = TRUE;
        } 
		//else if(i + 1 < argc) //+1 if 2 mandatory parameters
		else if(i + 6 < argc) //+6 if 7 mandatory parameters
		{
			//mandatory parameters
			channelid = atoi(argv[i]);
			//min(16, max(1, channelid)); //for user channelid is specified by an integer between 1 and 16
			min(15, max(0, channelid)); //for user channelid is specified by an integer between 0 and 15
			channelid_valid = TRUE;
			//channelid = channelid -1; //for the implementation channelid is specified by an integer between 0 and 15
			ccnumber = atoi(argv[i+1]);	
			min(127, max(0, ccnumber));
			ccnumber_valid = TRUE;
			ccstart = atoi(argv[i+2]);	
			min(127, max(0, ccstart));
			ccstart_valid = TRUE;
			ccend = atoi(argv[i+3]);	
			min(127, max(0, ccend));
			ccend_valid = TRUE;
			ccstep = atoi(argv[i+4]);	
			min(127, max(0, ccstep));
			ccstep_valid = TRUE;
			startdelay_ms = atoi(argv[i+5]);	
			min(127, max(0, startdelay_ms));
			startdelay_ms_valid = TRUE;
			serieduration_ms = atoi(argv[i+6]);	
			min(127, max(0, serieduration_ms));
			serieduration_ms_valid = TRUE;
			break;
		}
		else 
		{
            show_usage();
        }
    }

	ShellExecuteA(NULL, "open", global_begin, "", NULL, 0);

	#ifdef DEBUG
		if (sizeof(void *) == 8) 
			printf("64-bit machine.\n");
		else if (sizeof(void *) == 4) 
			printf ("32-bit machine.\n");
		printf("latency %ld\n", (long) latency);
		printf("device name %s\n", devicename);
		printf("channel id %ld\n", (long) (channelid+1));
		printf("cc number %ld\n", (long) ccnumber);
		printf("cc start %ld\n", (long) ccstart);
		printf("cc end %ld\n", (long) ccend);
		printf("cc step %ld\n", (long) ccstep);
		printf("start dalay %ld\n", (long) startdelay_ms);
		printf("serie duration %ld\n", (long) serieduration_ms);
	#endif //DEBUG
	if(channelid_valid==TRUE &&
		ccnumber_valid==TRUE &&
		ccstart_valid==TRUE &&
		ccend_valid==TRUE &&
		ccstep_valid==TRUE &&
		startdelay_ms_valid==TRUE &&
		serieduration_ms_valid ==TRUE)
	{

		if(latency_valid==FALSE)
		{
			latency = 0; //ms
		}
		if(devicename_valid==FALSE)
		{
			printf("warning wrong devicename format, replacing invalid devicename by default devicename\n");
			id = Pm_GetDefaultOutputDeviceID();
			info = Pm_GetDeviceInfo(id);
			strcpy(devicename, info->name);
			printf("device name %s\n", devicename);
		}
	}
	else
	{
		printf("warning invalid arguments format, exit(1)\n");
		show_usage();
	}

	deviceid = get_device_id(devicename, STRING_MAX);
	if(deviceid==-1) 
	{
		deviceid=Pm_GetDefaultOutputDeviceID();
		printf("warning wrong devicename syntax, replacing invalid devicename by default devicename\n");
		info = Pm_GetDeviceInfo(deviceid);
		strcpy(devicename, info->name);
		printf("device name %s\n", devicename);
	}

    /* send note */
    //midicontinuouscontroller_stream(latency, deviceid, close_mididevice_onexit, channelid, ccnumber, ccstart, ccend, ccstep, startdelay_ms, serieduration_ms);
    midicontinuouscontroller_nostream(latency, deviceid, close_mididevice_onexit, channelid, ccnumber, ccstart, ccend, ccstep, startdelay_ms, serieduration_ms);
	//main_test_output();

	ShellExecuteA(NULL, "open", global_end, "", NULL, 0);

    return 0;
}
