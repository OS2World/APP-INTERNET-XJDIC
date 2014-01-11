/**************************************************************************
*                     X  J  D  F R O N T E N D                            *
*                Common Frontend Routines for client & stand-alone vers.  *
*         Japanese-English Dictionary program (X11 version)               *
*                                                   Author: Jim Breen     *
***************************************************************************/
/*  This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 1, or (at your option)
    any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.     */

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <stdlib.h>
#include <signal.h>
#include <errno.h>
#include "xjdic.h"

/*    Paul Burchard supplied a patch to provide BSD compatibility for xjdic
(it uses the appropriate BSD ioctls in place of the SVR4 stuff).  In
order to enable this, people should compile with the option
-D__STRICT_BSD___ .         */

#ifdef __STRICT_BSD__
#include <sgtty.h>
#else
#ifdef __POSIX__
#include <sys/termios.h>
#else
#include <termio.h>
#endif
#endif

#define WINSIZE_IOCTL_AVAILABLE



static enum
{
IOCTL_ORIG,
IOCTL_RAW
} myi_status = IOCTL_ORIG;

#ifdef __STRICT_BSD__
static struct sgttyb    orig,new;
#else
static struct termio    orig,new;
#endif

extern unsigned char CBname[100];
extern unsigned char Dnamet[10][100],XJDXnamet[10][100];
extern unsigned char *dicbufft[10];
extern unsigned long diclent[10], indkent[10],indptrt[10];
extern int NoDics,CurrDic;
int thisdic = 0;
int gdicnos[10],gdicmax=0,GDmode=FALSE,gdiclen;
int GDALLmode=FALSE;

FILE *fe, *fex, *fclip, *fopen();

#ifdef XJDCLSERV
extern int portno;
extern unsigned char host[];
#endif

#ifdef XJDDIC
extern unsigned long dichits[10],dicmiss[10];
extern unsigned long indhits[10],indmiss[10];
extern unsigned long vbkills;
#endif

char DicDir[100];
int xfilelen;

pid_t pid;
int sig=SIGTSTP;
int ShiftJIS = FALSE,NoSJIS=FALSE;
unsigned char instr[256],radkanj[250][2];
int radnos[250];
unsigned char kanatab[NRKANA*2][7];
int Omode = 0,Smode = 0,Dmode = 0,AKanaMode;
int DRow,DCol,MaxY=MAXLINES,MaxX=MAXCOLS-1,KFlushRes,nok;
unsigned long hittab[NOHITS];
int verblen,DispHit,ksp,hitind,FirstKanj = 0,prieng = FALSE,Extopen=FALSE,NoSkip;
int extlen,extjdxlen;
unsigned char kmodes[2][10] = {"ON","OFF"};
unsigned char kmodes_r[2][10] = {"OFF","ON"};
unsigned long chline,chpos,it;
unsigned char strfilt[10],tempout[80];
unsigned char KSname[50] = {"kanjstroke"};
unsigned char RKname[50] = {"radkfile"};
unsigned char Rname[50] = {"radicals.tm"};
unsigned char ROMname[60] = {"romkana.cnv"};
unsigned char EXTJDXname[80] = {"edictext.xjdx"};
unsigned char EXTname[80] = {"edictext"};
unsigned char Vname[60] = {"vconj"};
unsigned char ENVname[100];
unsigned char cl_rcfile[100];
unsigned char Clip_File[100] = {"clipboard"};
unsigned char GPL_File[100] = {"gnu_licence"};
unsigned char KDNSlist[50];
int jiver = 14;		/*The last time the index structure changed was Version1.4*/
unsigned char sver[] = {SVER};
unsigned char fbuff[512],KLine[KFBUFFSIZE],karray[KANJARRAYSIZE][5];
unsigned char LogLine[200];
unsigned char ksch[50],ktarg[50];
/* The following Help table has "~" to force spaces   */
unsigned char Help[40][81] = {
"\n~~~~~~~~~~~~~~~~~~XJDIC USAGE SUMMARY ",
"At the SEARCH KEY prompt respond with a string of ascii, kana and/or ",
"kanji to look up in the current dictionary (prefix with @ or # to invoke ",
"conversion of romaji to hiragana or katakana)",
"~~~~~~~~~~~~~~~~~~SINGLE CHARACTER COMMANDS",
"~~\\ enter Kanji Dictionary mode~~~? ~~get this Help display",
"~~_ select dictionary files ~~~~~~=/^ cycle up/down dictionary files",
"~~\' set/clear one-off filter~~~~~~; activate/deactivate general filters",
"~~/ toggle kanji_within_compound~~- toggle long kanji display on/off",
"~~$ set global dictionaries ~~~~~~% toggle global search mode on/off",
"~~] display Dictionary Extension ~: toggle verb deinflection on/off",
"~~+ toggle priority English keys~~| toggle unedited display mode on/off",
"~~[ toggle exact_match on/off~~~~~& toggle kana input mode on/off",
"~~{ switch to clipboard input ~~~~} toggle reverse video of matches",
"~~` toggle multiple global disp.~~Ctrl-D  to exit",
"~~! display gnu licence~~~~~~~~~~~Ctrl-Z to suspend",
"~~~~~~Kanji Dictionary mode - prompt is KANJI LOOKUP TYPE:.  Responses:",
"~~a single kanji or a kana reading (default)",
"~~j followed by the 4-digit hexadecimal JIS code for a kanji",
"~~j followed by k and the 4-digit KUTEN code for a kanji",
"~~~~~~~(precede code with `h' for JIS X 0212 kanji.)",
"~~j followed by s and the 4-digit hexadecimal Shift-JIS code for a kanji",
"~~m followed by an (English) kanji meaning",
"~~c followed by an index code such as Nnnn (Nelson), Bnn (Bushu), etc",
"~~r initiates a display of all radicals and their numbers",
"~~l switches the program into the Radical Lookup mode",
"$$$"
};
unsigned char RVon[] = {0x1b,'[','7','m',0};
unsigned char RVoff[] = {0x1b,'[','m',0};
int nofilts=FALSE,filton[NOFILT],filtact[NOFILT],filttype[NOFILT],filtcoden[NOFILT];
unsigned char filtnames[NOFILT][50],filtcodes[NOFILT][10][10];
unsigned char testline[1025],SingleFilter[50];
unsigned char vdicf[VMAX][7],vinfl[VMAX][21],vcomms[41][50];
int strf,Jverb = TRUE,SFFlag=FALSE,vcommno[VMAX];
int ROmode = 1,EMmode = 1,KLmode = 1,KImode = 1,KLRmode,KLcount;
unsigned char vline[250],vstr[13];
unsigned char RadK1[300],RadK2[300],*RKanj1,*RKanj2,*RKSet[10];
unsigned char RKTarg[21];
int rmax,NoSets=0,NoRads,RKStart[300],RKCnt[300];
unsigned char ops[3],kstrokes[7000];
int kstrokelim,kstroketype;
int clipmode=FALSE;
unsigned char clipstring1[51];
unsigned char clipstring2[51]={"XXXX"};
int RVACTIVE = TRUE;

int DicNum;
long DicLoc;

/*====== Prototypes========================================================*/

FILE  *xfopen(char *file_name, char *file_mode, int *xfilelen);
int getcharxx();
void RadDisp();
void RadBuild();
int FindRad(unsigned char char1, unsigned char char2);
void DoLOOKUP();
void RadLoad();
void KSLoad();
void xjdserver (int type, int dic_no, long index_posn, int sch_str_len, 
		unsigned char *sch_str, int *sch_resp, long *res_index, 
		int *hit_posn, int *res_len, unsigned char *res_str,
		long *dic_loc );
void OneShot();
void RadSet();
void Verbtoggle();
void FiltSet();
void xjdicrc();
void DoRADICALS();
int Vlookup();
void AppKanji(unsigned char c1,unsigned char c2);
void Verbinit();
void KOut(unsigned char *sout);
void LoadKana();
void DoRomaji(unsigned char kc);
int kanaconv(int rpos, int rlen);
void togglemode();
void engpritoggle();
void altdic(int dicincr);
void DoKANJI();
void DoJIS();
int addhit(long spot);
void GetEUC(unsigned char *eucline);
void cbreakon();
void cbreakoff();
void ioctlorig();
void ioctlraw();
void Lookup();
void Lookup2();
void DicSet();
void sjis2jis(int *p1,int *p2);/* Ken Lunde's routine  */
void jis2sjis(unsigned char *p1,unsigned char *p2);/* Ken Lunde's routine  */
int stringcomp(unsigned char *s1, unsigned char *s2);
void FixSJIS(unsigned char *jline);
void GetKBStr(unsigned char *prompt);
void ExtFileDisp();
void SeekErr(int iores);
void KOutc(int c);
void KLookup();
int KFlush(unsigned char *msg);
int KEOS (unsigned char *msg);
void NewWinSize();
int kcmp (unsigned char *t1, unsigned char *t2);
unsigned char *DicName(int dn);
/*====== end of prototypes==================================================*/


/* ==== ioctl routines supplied by Cameron Blackwood=======================*/
/* ==== BSD compatibility hacked in by Paul Burchard ==============*/
/*	These routines are to disable/re-enable "cbreak", when I want to
	switch in & out of canonical input processing. Mostly xjdic does
	not use canonical input, as I want to react immediately to most	
	key-presses		*/

void    ioctlraw()
{
  if (myi_status == IOCTL_ORIG)
  {
#ifdef __STRICT_BSD__
    ioctl(0, TIOCGETP, &orig); ioctl(0, TIOCGETP, &new);
    new.sg_flags |= CBREAK; new.sg_flags &= ~ECHO;
    ioctl(0, TIOCSETP, &new);
#else
    ioctl(0, TCGETA, &orig); ioctl(0, TCGETA, &new);
    new.c_lflag &= ~ICANON; new.c_lflag &= ~ISIG; new.c_lflag &= ~ECHO;
    new.c_lflag &= ~IXON;
    new.c_cc[4] = 1; new.c_cc[5] = 0;   ioctl(0, TCSETA, &new);
#endif
    myi_status=IOCTL_RAW;
  }
  else return;
}

void    ioctlorig()
{
#ifdef __STRICT_BSD__
   ioctl(0, TIOCSETP, &orig);
#else
   ioctl(0, TCSETA, &orig);
#endif
    myi_status = IOCTL_ORIG;
}


void cbreakoff()
{
	ioctlorig();
	/*system("stty -cbreak echo");*/
}

void cbreakon()
{
	ioctlraw();
	/*system("stty cbreak -echo");*/
}

int getcharxx()
{
	if (clipmode)
	{
		return('n');
	}
	else
	{
		return(getchar());
	}
}
/*====GetWinSize==== Hank Cohen's routine for getting the (new) window size==*/
/*
 * (The following was supplied by Hank Cohen)
 * We would like to use the Berkeley winsize structure to determine
 * the number of lines and columns in the window.  If that's not
 * available we can use termcap.
 * If using termcap, you will need to compile with "-lcurses -ltermcap".
 */
char termcap_buf[1024];
void GetWinSize()
{
	char *term_name;

#ifdef WINSIZE_IOCTL_AVAILABLE
	struct winsize window;

	signal(SIGWINCH, NewWinSize);
	ioctl(0,TIOCGWINSZ,&window);
	MaxX = window.ws_col;
	MaxX--;
	MaxY = window.ws_row;
#else /* Use termcap */
	if ((term_name = getenv("TERM")) == 0){
		fprintf(stderr,"No TERM in environment!\n");
	} else if (tgetent(termcap_buf, term_name) != 1) {
		fprintf(stderr,"No termcap entry for %s!\n", term_name);
	} else {
		MaxX = tgetnum("co");
		MaxY = tgetnum("li");
	}
#endif  /* termcap */
}
void NewWinSize()
{
	struct winsize window;
	ioctl(0,TIOCGWINSZ,&window);
	MaxX = window.ws_col;
	MaxX--;
	MaxY = window.ws_row;
}

/*=====KSLoad===Load file of kanji/stroke data==========================*/
void KSLoad()
{
	int i,j,k,lno;
	FILE *fk,*fopen();

	fk = xfopen(KSname,"r",&xfilelen);
	lno=0;
	while(!feof(fk))
	{
		fgets(testline,9,fk);
		if(feof(fk)) break;
		testline[3] = 0;
		lno++;
		i = ((testline[0] & 0x7f)-0x30)*94 + ((testline[1] & 0x7f) - 0x21);
		if ((i < 0) || (i > 6999))
		{
			printf("Bad kanji in %s at line %d (%s)\n",KSname,lno,testline);
			i = 6999;
		}
		kstrokes[i] = testline[2]-'0';
	}
	fclose(fk);
}

/*=====RadLoad===Load file of Radical Data==============================*/
void RadLoad()
{
	int i,j,k;
	FILE *fk,*fopen();

	fk = xfopen(RKname,"r", &xfilelen);
	k = xfilelen/2;
	RKanj1 = malloc(k*sizeof(char));
	if (RKanj1==NULL)
	{
		printf("malloc failed for radical tables!\n");
		exit(1);
	}
	RKanj2 = malloc(k*sizeof(char));
	if (RKanj2==NULL)
	{
		printf("malloc failed for radical tables!\n");
		exit(1);
	}
	i = -1;
	j = 0;
	rmax = 0;
	while(!feof(fk))
	{
		fgets(testline,199,fk);
		if(feof(fk)) break;
		if (testline[0] == '$')
		{
			i++;
			RadK1[i] = testline[2];
			RadK2[i] = testline[3];
			RKStart[i] = j;
			RKCnt[i] = 0;
			if (i != 0)
			{
				if (RKCnt[i-1] > rmax) rmax = RKCnt[i-1];
			}
		}
		else
		{
			for (k = 0; k < strlen(testline); k++)
			{
				if (testline[k] < 127) continue;
				RKanj1[j] = testline[k];
				RKanj2[j] = testline[k+1];
				RKCnt[i]++;
				j++;
				k++;
			}
		}
	}
	fclose(fk);
	NoRads = i;
	for (i=0; i<10;i++)
	{
		RKSet[i] = malloc(2*rmax+1);
		if (RKSet[i] == NULL)
		{
			printf("malloc() failed for Radical set(s)!\n");
		}
	}
}
/*=====DoRomaji==collect search key from keyboard. Convert to kana.======*/
/*	Code originally from JDIC			*/
void DoRomaji(unsigned char kc)
{
	int is;
	unsigned char c;

/* collect the search string   */
  Smode = 1;
  if(kc == '#') Smode = 2;
  is = 0;
  ksp = 0;
  c = 0;
  ktarg[0] = 0;
  printf("\r                                         \r%sROMAJI ENTRY:%s ",RVon,RVoff);
  while (c != 0x0a)	  /* loop until Enter is pressed   */
  {
	c = getcharxx();

	if ((c == 0x8)||(c == 0x7f))  /* backspace  */
	{
			if (is != ksp)  /* kana mode - back over a romaji  */
			{
				ksch[is-1] = '\0';
				is--;
  				sprintf(tempout,"\r                                     \r%sROMAJI ENTRY:%s %s%s",RVon,RVoff,ktarg,ksch+ksp);
				KOut(tempout);
				continue;
			}
			else
			{
				if (strlen(ktarg) != 0)  /* kana mode - back over a kana  */
				{
					ktarg[strlen(ktarg)-2] = '\0';
  					sprintf(tempout,"\r                                     \r%sROMAJI ENTRY:%s %s%s",RVon,RVoff,ktarg,ksch+ksp);
					KOut(tempout);
					continue;
				}
			}
	}
	if (c > 32)   /* ordinary character - store and display   */
	{
		ksch[is] = c | 0x20;
		ksch[is+1] = '\0';
		is++;
  		sprintf(tempout,"\r                                     \r%sROMAJI ENTRY:%s %s%s",RVon,RVoff,ktarg,ksch+ksp);
		KOut(tempout);
  	}
	if (ksp != is)
	{

/* the input string so far is now parsed for romaji -> kana conversions.
   function "kanaconv" is used for the various sub-strings    */

/* if there is an "nn", "nm" or "mm", convert to first to "q" to force it to be
   converted to a kana "n"   */
		if ((ksch[ksp] == 'n')&&(ksch[ksp+1] == 'n')) ksch[ksp] = 'q';
		if ((ksch[ksp] == 'm')&&(ksch[ksp+1] == 'm')) ksch[ksp] = 'q';
		if ((ksch[ksp] == 'n')&&(ksch[ksp+1] == 'm')) ksch[ksp] = 'q';
/* if there is "nx", where "x" is not a vowel or a "y", force the "n".  */
		if (((ksch[ksp] == 'n')||(ksch[ksp] == 'm'))&&(ksch[ksp+1] != 0))
		{
			c = ksch[ksp+1];
			if((c!='y')&&(c!='a')&&(c!='e')&&(c!='i')&&(c!='o')&&(c!='u')&&(c!='\''))
			{
				ksch[ksp] = 'q';
			}
		}
		if(kanaconv(ksp,1))  /*  match on a,e,i,o,u,q or -  ?  */
		{
			continue;
		}
		if(ksch[ksp] == '\'')
		{
			ksp++;
			continue;
		}
		if (ksch[ksp] == ksch[ksp+1])  /* double consonant - force small
						 "tsu" */
		{
			ksch[ksp] = '*';
			kanaconv(ksp,1);
			continue;
		}
		if(kanaconv(ksp,2))  /* match on two letter syllable   */
		{
			continue;
		}
		if(kanaconv(ksp,3))  /*match on 3 letter syllable    */
		{
			continue;
		}
		if(kanaconv(ksp,4))  /*match on 4 letter syllable    */
		{
			continue;
		}
	}		/* end of rom->kana */
  }			/* end of while loop */
  if (ksch[ksp] =='n')  /*flush out a trailing "n"*/
  {
	ksch[ksp] = 'q';
	kanaconv(ksp,1);
  }

  strcpy(instr,ktarg);
}

/*========kanaconv==convert romaji to kana==============================*/
/*	More code from JDIC			*/
int kanaconv(int rpos, int rlen)
{
/* rpos and rlen are the start and length of the romaji characters in
   array ksch.  Smode specifies hira or kata. If found, the kana is
   appended to ktarg and TRUE returned.                          */

	int koff,ki;
	unsigned char targ[50];

	koff = (Smode-1)*NRKANA;
	for(ki = 0; ki < rlen; ki++)
	{
		targ[ki] = ksch[rpos+ki];
	}
	targ[rlen] = 0;
	for (ki = koff; ki < koff+NRKANA; ki+=2)
	{
		if (strlen(targ) != strlen(kanatab[ki])) continue;
		if (stringcomp(targ,kanatab[ki]) != 0) continue;
		strcat(ktarg,kanatab[ki+1]);
		ksp = ksp+rlen;
  		sprintf(tempout,"\r                                     \r%sROMAJI ENTRY:%s %s%s",RVon,RVoff,ktarg,ksch+ksp);
		KOut(tempout);
		return (TRUE);
	}
	return(FALSE);
}

/* ==== LoadKana=== Load the romaji to kana conversion file============*/
void LoadKana()
{
	int i,ih,mode;
	FILE *fp,*fopen();
	unsigned char LKin[80],*ptr;

	for (i = 0; i < NRKANA*2; i++) strcpy(kanatab[i]," ");
	fp = xfopen(ROMname,"r", &xfilelen);
	mode = 0;
	while (!feof(fp))
	{
		fgets(LKin,79,fp);
		if (feof(fp))break;
		/*LKin[strlen(LKin)-1] = '\0';*/
		if(LKin[0] == '#')continue;
		if((LKin[0] == '$')&&((LKin[1]|0x20) == 'h'))
		{
			mode = 0;
			ih = 0;
			continue;
		}
		if((LKin[0] == '$')&&((LKin[1]|0x20) == 'k'))
		{
			mode = 1;
			ih = 0;
			continue;
		}
		ptr = (unsigned char *)strtok(LKin," \t");
		if ( ptr != NULL ) strcpy(kanatab[mode*NRKANA+ih*2+1],ptr);
		ptr = (unsigned char *)strtok(NULL," \t\r\n");
		if ( ptr != NULL ) strcpy(kanatab[mode*NRKANA+ih*2],ptr);
		ih++;
		if(ih == NRKANA) 
		{
			printf("Too many romaji table entries!");
			exit(1);
		}
	}
	fclose(fp);
}
/*======jis2sjis  (from Ken Lunde) =====================================*/
void jis2sjis(unsigned char *p1,unsigned char *p2) /* courtesy of Ken Lunde */
{
    register unsigned char c1 = *p1;
    register unsigned char c2 = *p2;
    register int rowOffset = c1 < 95 ? 112 : 176;
    register int cellOffset = c1 % 2 ? 31 + (c2 > 95) : 126;

    *p1 = ((c1 + 1) >> 1) + rowOffset;
    *p2 = c2 + cellOffset;
}

/*====KEOS===End of screen processing for KFlush==================*/
int KEOS (unsigned char *msg)
{
	unsigned char ck;

	if (DRow < MaxY-2) return(TRUE);
	DRow = 0;
	if (strlen(msg) == 0) return (TRUE);
	printf("%s\n",msg);
	ck = getcharxx();
	if ((ck == 'n')||(ck == 'N')) return (FALSE);
	if ((ck == 'y')||(ck == 'Y')) return (TRUE);
	if ((ck != 0xa) && (ck != 0xd)) ungetc(ck,stdin);
	return (FALSE);
}
/*====KFlush==== Output a line, folding if necessary===============*/
/*	This is now the main screen output routine. An array "KLine"
	is built up of text to be output. KFlush() sends it to the screen,
	folding the line at white-space if it is about to hit the RHS.
	It also tests for end of screen, and prompts for continuation,
	using the KEOS(). Returns TRUE for continue, and FALSE for 
	stopping.  
	Called with the prompt measseage.			*/

int KFlush(unsigned char *msg)
{
	unsigned char *kptr,ktemp[512];
	int retf,it,j;
	int Test;

	if (strlen(KLine) == 0) return (TRUE);
	kptr = (unsigned char *)strtok(KLine," ");
	while (kptr != NULL)
	{
		Test = MaxX;
		strcpy(ktemp,kptr);
		if (ktemp[0] == '\t')
		{
			it = DCol % 10;
			if (it != 0) 
			{
				DCol = DCol+10-it;
				if (DCol <= Test-1)
				{
					for (j = 0;j < 10-it;j++) KOut(" ");
				}
			}
			strcpy(ktemp,ktemp+1);
		}
		it = strlen(ktemp);
		if (DCol+it < Test)
		{
			DCol = DCol+it+1;
		}
		else
		{
			KOut("\n");
			DRow++;
			DCol=it+1;
			retf = KEOS(msg);
			if (!retf) return (FALSE);
		}
		KOut(ktemp);
		if (DCol <= MAXCOLS) KOut(" ");
		kptr = (unsigned char *)strtok(NULL," ");
	}
	KOut("\n");
	DRow++;
	retf = KEOS(msg);
	DCol = 0;
	if (!retf) return (FALSE);
	return (TRUE);
}
/*====KOutc===add a character to KLine=============================*/
void KOutc(int c)
{
	unsigned char tmp[2];
	tmp[0] = c;
	tmp[1] = 0;
	strcat(KLine,tmp);
	return;
}

/*=====KOut===output kana/kanji according to selected mode===========*/
/*	Mostly called from KFlush. Outputs the parameter string, in the
	specified JIS mode.					*/
void KOut(unsigned char *sout)
{
	int i;
	unsigned char c1,c2;

	for (i = 0; i < strlen(sout); i++)
	{
		c1 = sout[i]; c2 = sout[i+1];
		if (c1 < 127)
		{
			if (c1 == '~') c1 = ' ';
			printf("%c",c1);
			continue;
		}
		switch(Omode)
		{
		case 0 :  /* JIS (default)  */
			if (c1 == 0x8f)
			{
				printf("%c$(D%c%c%c(B",0x1b,c2&0x7f,sout[i+2]&0x7f,0x1b);
				i+=2;
				break;
			}
			printf("%c$B%c%c%c(B",0x1b,c1&0x7f,c2&0x7f,0x1b);
			i++;
			break;

		case 1 : /* EUC (internal format) */
			if (c1 == 0x8f)
			{
				printf("%c%c%c",c1,c2,sout[i+2]);
				i+=2;
				break;
			}
			printf("%c%c",c1,c2);
			i++;
			break;

		case 2 : /* Shift-JIS */
			c1 -= 128; c2 -= 128;
			jis2sjis(&c1,&c2);
			printf("%c%c",c1,c2);
			i++;
			break;
		}
	}
}

/*======function to test if this entry has already been displayed=====*/
int addhit(long spot)
{
	int i;

	if (spot == 0) return(TRUE);

	for (i=0;i<=hitind;i++)
	{
		if(hittab[i] == spot) return(FALSE);
	}
	if(hitind < NOHITS) hitind++;
	hittab[hitind] = spot;
	return(TRUE);
}

/*====GetEUC - ensures that any JIS in the string is EUC ============*/
/*      Based on the GetEUC in JREADER, this routine examines
	the string "instr" and converts any JIS or SJIS to EUC.
	The result is placed in the specified string.        */

void GetEUC(unsigned char *eucline)
{
	int i,j,SI,J212,J212sw;

	J212 = FALSE;
	eucline[0] = '\0';
	chline = 0;
	chpos = 0;
	SI = FALSE;
	ShiftJIS = FALSE;
	j = 0;
	for (i = 0; i < strlen(instr); i++)
	{
		if((instr[i]==0x1b)&&(instr[i+1]=='$')&&(instr[i+2]=='(')&&(instr[i+3]=='D'))
		{
			SI = TRUE;
			J212 = TRUE;
			J212sw = 0;
			NoSJIS = TRUE;
			i+=3;
			continue;
		}
		if((instr[i]==0x1b)&&(instr[i+1]=='$')&&(instr[i+2]=='B'))
		{
			SI = TRUE;
			J212 = FALSE;
			i+=2;
			continue;
		}
		if((instr[i]==0x1b)&&(instr[i+1]=='$')&&(instr[i+2]=='@'))
		{
			SI = TRUE;
			J212 = FALSE;
			i+=2;
			continue;
		}
		if((instr[i]==0x1b)&&(instr[i+1]=='(')&&(instr[i+2]=='J'))
		{
			SI = FALSE;
			J212 = FALSE;
			i+=2;
			continue;
		}
		if((instr[i]==0x1b)&&(instr[i+1]=='(')&&(instr[i+2]=='B'))
		{
			SI = FALSE;
			J212 = FALSE;
			i+=2;
			continue;
		}
		if (instr[i] == '\0')break;
		if (SI)
		{
			if (J212 && (J212sw == 0)) eucline[j++] = 0x8f;
			eucline[j] = instr[i] | 0x80;
			J212sw = (J212sw+1) % 2;
		}
		else
		{
			eucline[j] = instr[i];
		}
		j++;
		eucline[j] = '\0';
	}
/*  fix up SHIFT-JIS, if present  */
	if (!NoSJIS) FixSJIS(eucline);
}

/*====FixSJIS=== convert any SJIS to EUC in a string==================*/
void FixSJIS(unsigned char *jline)
{
	int i,p1,p2,ShiftJIS;

	ShiftJIS = FALSE;
	for (i = 0; i < strlen(jline); i++)
	{
		p1 = jline[i];
		if (p1 < 127)continue;
		p2 = jline[i+1];
        	if ((p1 >= 129) && (p1 <= 159)) ShiftJIS = TRUE;
		if (((p1 >= 224) && (p1 <= 239))&& ((p2 >= 64) && (p2 <= 158))) ShiftJIS = TRUE;
		if (ShiftJIS)
		{
            		sjis2jis   (&p1,&p2);
            		p1 += 128;
            		p2 += 128;
			jline[i] = p1;
			jline[i+1] = p2;
		
		}
		i++;
	}
}

/*===sjis2jis    - convert ShiftJIS to JIS ===========================*/

void sjis2jis   (int *p1,int *p2)   /* Ken Lunde's routine  */
{
    register unsigned char c1 = *p1;
    register unsigned char c2 = *p2;
    register int adjust = c2 < 159;
    register int rowOffset = c1 < 160 ? 112 : 176;
    register int cellOffset = adjust ? (31 + (c2 > 127)) : 126;

    *p1 = ((c1 - rowOffset) << 1) - adjust;
    *p2 -= cellOffset;
}

/*====ExtFileDisp===Display from EDICTEXT file=======================*/

void ExtFileDisp()
{

	unsigned extrec[2],seekoff,iores,hi,lo,mid,ejdxtest[2];
	unsigned char Ssch[20];
	int bsres,i;

    printf("%sExtension Key:%s ",RVon,RVoff);

	GetKBStr("Extension Key:");
	if(fbuff[0] < 128) 
	{
		printf("\nThe extension file has Kanji & Kana keys\n");
		return;
	}
	if(!Extopen)
	{
		fe = xfopen(EXTname,"rb", &extlen);
        	fex  = xfopen(EXTJDXname,"rb", &extjdxlen);
		Extopen = TRUE;
		extlen++;
		fread(ejdxtest,sizeof(long),1,fex);
		if (ejdxtest[0] != (extlen+jiver))
		{
			printf("\nEDICT Extension file & Index Mismatch! %ld %ld\n",ejdxtest[0],extlen+jiver);
			exit(1);
		}
	}

	lo = 0;
	hi = (extjdxlen/(2*sizeof(long)))-1;
	while(TRUE)
	{
		mid = (lo+hi)/2;
		seekoff = mid;
		seekoff *= (2*sizeof(long));
		seekoff+=sizeof(long);
		if((iores = fseek(fex,seekoff,SEEK_SET)) != 0)SeekErr(iores);
		iores = fread(&extrec,sizeof(long),2,fex);
		seekoff = extrec[0];
		if((iores = fseek(fe,seekoff,SEEK_SET)) != 0)SeekErr(iores);
		iores = fread(&Ssch,sizeof(char),19,fe);
		Ssch[19] = 0;
		i = 0;
		bsres = 0;
		for (i = 0; Ssch[i] != 0 ;i++)
		{
			if (Ssch[i] < 128) break;
			if (fbuff[i] < 128) break;
			if (fbuff[i] < Ssch[i])
			{
				bsres = -1;
				break;
			}
			if (fbuff[i] > Ssch[i])
			{
				bsres = 1;
				break;
			}
		}
		if ((bsres != 0) && ((lo + hi) == 0)) break;
		if(bsres < 0)
		{
			if (mid == 0) break;
			hi = mid-1;
		}
		else
		{
			lo = mid+1;
		}
		if (bsres  == 0) break;
		if (lo > hi) break;
		if (hi < 0) break;
	}
	if (bsres == 0)
	{
		printf("\n%sDictionary Extension Display%s\n",RVon,RVoff);
		seekoff = extrec[1];
		if((iores = fseek(fe,seekoff,SEEK_SET)) != 0)SeekErr(iores);
		strcpy (KLine," <");
		DRow = 0;
		DCol = 0;
		while(!feof(fe))
		{
			fgets(LogLine,199,fe);
			if (feof(fe)) break;
			if ((LogLine[0] == '<') && (LogLine[1] > 128)) break;
			for (i = strlen(LogLine); i >= 0; i--)
			{
				if (LogLine[i] < 0x20) LogLine[i] = 0;
			}
			strcat(KLine,LogLine);
			if (!KFlush("Continue displaying extension information? (y/n)")) break;
			DCol = 0;
			strcpy (KLine," ");
		}
		return;
	}
	if (bsres != 0)
	{
		printf("\nNot found in Extension file!\n");
		return;
	}
}
/*====kcmp === comparison routine for qsort for kanji table==========*/
int kcmp (unsigned char *t1, unsigned char *t2)
{
	int i,cmp;
	for (i=0;i<4;i++)
	{
		cmp = t1[i] - t2[i];
		if (cmp == 0) continue;
		return(cmp);
	}
	return(0);
}

/*==== Verbinit===Load & initialize verb inflection details==========*/
void Verbinit()
{
	unsigned char tempstr[512],*vptr;
	int vmode,i;
	FILE *fi,*fopen();
	
	for (i = 0;i< VMAX;i++)
	{
		vdicf[i][0] = 0;
		vinfl[i][0] = 0;
		vcommno[i] = 40;
	}
	for (i = 0;i<40;i++)
	{
		vcomms[i][0] = 0;
	}
	vmode = 1;
	strcpy(vcomms[40],"Unknown type");
	verblen = 0;
	fi = xfopen(Vname,"r", &xfilelen);
	while(TRUE)
	{
		fgets(tempstr,511,fi);
		if(feof(fi))break;
		if (tempstr[0] == '#')continue;
		if (tempstr[0] == '$')
		{
			vmode = 2;
			continue;
		}
		
		switch (vmode) {
		case 1 :
			vptr = (unsigned char *)strtok(tempstr," \t\n\r");
			i = atoi(vptr);
			if ((i < 0) || (i > 39)) break;
			vptr = (unsigned char *)strtok(NULL,"\t\n\r");
			strcpy(vcomms[i],vptr);
			break;	
		case 2 :	
			vptr = (unsigned char *)strtok(tempstr," \t\n\r");
			strcpy(vinfl[verblen],vptr);
			vptr = (unsigned char *)strtok(NULL," \t\n\r");
			strcpy(vdicf[verblen],vptr);
			vptr = (unsigned char *)strtok(NULL," \t\n\r");
			i = atoi(vptr);
			if ((i >= 0)&&(i <= 40)) vcommno[verblen] = i;
			verblen++;
			if (verblen==VMAX)
			{
				printf("Verb data overflow. Ignoring following entries\n");
				verblen--;
				fclose(fi);
				return;
			}
			break;
		}
	}
	verblen--;
	fclose(fi);
}

/*=== append a kana/kanji to the verb display line================*/
void AppKanji(unsigned char c1,unsigned char c2)
{
	unsigned char ops[3];

	ops[0] = c1;
	ops[1] = c2;
	ops[2] = 0;
	strcat(vline,ops);
}

/*=======Vlookup== look up plain form verb in dictionary=============*/
int Vlookup()
{

	int xjresp,roff,rlen;
	unsigned char repstr[512];
	long respos;
	int hit,schix;
	unsigned char khi,klo,cc,ops[4];
	long it;

	DicNum = CurrDic;
	khi = 0;
	klo = 0;
	vline[0] = 0;
	xjdserver (XJ_FIND, DicNum,it, strlen(vstr), vstr, 
		&xjresp, &respos, &roff, &rlen, repstr, &DicLoc);
	if (xjresp != XJ_OK) return (FALSE);
	it = respos;
	while (xjresp == XJ_OK)
	{
		if (roff != 0)
		{
			it++;
			xjdserver (XJ_ENTRY, DicNum, it, strlen(vstr), vstr, 
				&xjresp, &respos, &roff, &rlen, repstr, &DicLoc);
			continue;
		}
		schix = 0;
		/* now work forwards, displaying the line  */
		hit = FALSE;
		/* If the first word has already been displayed, skip it.
	   	Otherwise, put braces around the first word (kanji)  */
		while (TRUE)
		{
			cc = repstr[schix];
			if (cc < 32) break;
			/* put a () around the yomikata in an ascii or Kanji search */
			if (cc=='[')
			{
				AppKanji(0xa1,0xcA);  /* EUC (  */
				schix++;
				continue;
			}
			if (cc==']')
			{
				AppKanji(0xA1,0xCB);  /* EUC )  */
				schix++;
				continue;
			}
			if (cc < 128) /* non-Japanese, display it
					(fix up the "/") */
			{
				ops[0]= cc;
				ops[1] = '\0';
				if (ops[0] == '/')
				{
					if (hit)
					{
						ops[0] = ',';
						ops[1] = ' ';
						ops[2] = '\0';
					}
					else
					{
						hit = TRUE;
						ops[0] = '\0';
					}
				}
				strcat(vline,ops);
			}
			else
			{
				if (cc == 0x8f)
				{
					AppKanji(cc,0);
					schix++;
					continue;
				}
				if (khi == 0)
				{
					khi = cc;
				}
				else
				{
					klo = cc;
					AppKanji(khi,klo);
					khi = 0;
					klo = 0;
				}
			}
			schix++;
		}
        	if(strlen(vline) > 0) break;
     	}
     	if(strlen(vline) <=1) return(FALSE);
     	return(TRUE);
}
/*=========== slencal - calculate the actual search string length ===*/
/*   This routine exists to sort out the actual length of the search
string when there is a mix of 2 and 3-byte EUC characters   */

int slencal (int noch, unsigned char *targ)
{
	int i,j;

	if (targ[0] < 127) return(noch+1);
	i = 0;
	j = 0;
	while(i <= noch)
	{
		if (targ[j] == 0x8f) j++;
		i++;
		j+=2;
	}
	return(j);
}

/*=========== Lookup - global frontend to dictionary search ========*/
void Lookup()
{
	int gi,dicsav,gdiclenbest;
	unsigned char retsave[KFBUFFSIZE],rethdr[5];

	retsave[0] = 0;
	gdiclen = 0;
	gdiclenbest = 0;
	if ((!GDmode) || (Dmode == 1))
	{
		Lookup2();
		return;
	}
	if (gdicmax == 0)
	{
		printf("\nNo global dictionaries specified - disabling!\n");
		GDmode = FALSE;
		Lookup2();
		return;
	}
	dicsav = CurrDic;
	for (gi=0;gi<=gdicmax;gi++)
	{
		CurrDic = gdicnos[gi];
		Lookup2();
		if (GDALLmode)
		{
			strcpy(retsave,KLine);
			strcpy(rethdr,"[X] ");
			rethdr[1] = '0'+gdicnos[gi];
			strcpy(KLine,rethdr);
			strcat(KLine,retsave);
			KFlush("");
			continue;
		}
		if ((gdiclen > gdiclenbest) || ((strlen(KLine) > strlen(retsave)) && (gdiclen == gdiclenbest)))
		{
			strcpy(retsave,KLine);
			strcpy(rethdr,"[X] ");
			rethdr[1] = '0'+gdicnos[gi];
			gdiclenbest = gdiclen;
		}
	}
	if (GDALLmode)
	{
		CurrDic = dicsav;
		return;
	}
	strcpy(KLine,rethdr);
	strcat(KLine,retsave);
	KFlush("");
	CurrDic = dicsav;
}



/*=========== Lookup2 - carry out dictionary search ================*/
void Lookup2()
{
/*

Carries out a search for matches with the string "fbuff" in the specified
dictionary. It matches the full string, then progressively shortens it.

*/
  	int schix,schiy,schiz,j,dind,hit,skip,brace,engrv;
  	int EngFirst;
	int slk,slen,slenx,i,srchlen,srchlenok;
  	unsigned int khi,klo,cc;
  	unsigned long zz,bshit[20];
  	unsigned char *kptr,*kptr2, k1,k2,kanj1,kanj2,kanj3;
	int FiltOK;
	unsigned char vlast[11],temp[11],ops[80];
	int vi,vok,prevch,KDNSflag,KDskip,KTest;
	int xjresp,roff,rlen;
	unsigned char repstr[512];
	unsigned long respos;

	vlast[0] = 0;
	KLcount = 0;
	DRow = 3;

	if (!GDmode && (Dmode == 0)&&Jverb&&(fbuff[0] > 0xa8) && (fbuff[2] < 0xa5) && (fbuff[4] < 0xa5))
	{
	/* possible inflected verb or adjective, so look up the verb table
	   for a matching plain form, and serch the dictionary for it      */

		vstr[0] = fbuff[0];
		vstr[1] = fbuff[1];
		vstr[2] = 0;
		for(i=0;i<11;i++) temp[i] = fbuff[i];

		for (vi = 0;vi <= verblen;vi++)
		{
			vok = TRUE;
			vstr[2] = 0;
			for (i = 0;i < strlen(vinfl[vi]);i++)
			{
				if (fbuff[2+i] != vinfl[vi][i])
				{
					vok = FALSE;
					break;
				}
			}
			if (!vok) continue;
			strcat(vstr,vdicf[vi]);
			
			if(strcmp(vstr,temp) == 0) continue;
			if (strcmp(vstr,vlast) == 0)continue;
			if (Vlookup())
			{
				strcpy(vlast,vstr);
				printf(" Possible inflected verb or adjective: (%s)\n",vcomms[vcommno[vi]]);				
				strcpy(KLine,vline);
				DCol = 0;
				KFlush("");

				printf("Continue with this search (y/n)\n");
				cc = getcharxx();
				if ((cc == 'n')||(cc == 'N')) return;
				if ((cc != 'y')&&(cc != 'Y'))
				{
					ungetc(cc,stdin);
					return;
				}
				DRow = 1;
			}		
		}
  	}
	/*  do a binary search through the index table looking for a match  */
	KLine[0] = 0;
	DCol = 0;
	nok = 0;
	DispHit = FALSE;
  	khi = 0;
  	klo = 0;
	DicNum = CurrDic;
	if(Dmode !=0) DicNum = 0;
	if (fbuff[strlen(fbuff)-1] < 32) fbuff[strlen(fbuff)-1] = 0;
	for (slenx = 1; slenx < 20; slenx++)
	{
		if (slencal(slenx-1,fbuff) >= strlen(fbuff)) break;
	}
	Smode = 0;
	if ((fbuff[0] == 0xa4)||(fbuff[0] == 0xa5)) 
	{
		Smode = 1;
		for (i = 0; i < strlen(fbuff); i+=2)
		{
			if (fbuff[i] > 0xa5)
			{
				Smode = 0;
				break;
			}
		}
	}
	srchlenok = 0;
  	for ( slen = 0; slen <slenx; slen++)
  	{
		srchlen = slencal(slen,fbuff);
  		xjdserver (XJ_FIND, DicNum, zz, srchlen, fbuff, 
			&xjresp, &respos, &roff, &rlen, repstr, &DicLoc);
/* printf("F: Returning: %d %ld %d %d %s\n",xjresp,respos,roff,rlen,repstr); */
  		if (xjresp == XJ_OK) 
  		{
  			bshit[slen] = respos;
  			srchlenok = srchlen;
  			continue;
  		}
  		else
  		{
  			break;
  		}
	}
  	if (slen == 0)
  	{
		if (!GDmode) printf("No Match Found\n");
		return;
  	}
	if (EMmode == 0) 
	{
		if (srchlenok != strlen(fbuff))
		{
			printf("No Match Found (Exact Test)\n");
			return;
		}
		if (((fbuff[0] <127) && isalnum(repstr[roff+srchlenok])) 
			||((fbuff[0] >=0xa4) && (repstr[roff+srchlenok] > 127)))
		{
			printf("No Match Found (Exact Test)\n");
			return;
		}
	}
  	hitind = 0;
  	hittab[0] = -1;
	gdiclen = slen*2;
	/*  loop for each possible string length  */
	for (dind = slen-1; dind >= 0 ; dind--)
	{
		/* this is the display loop - usually one line per entry  */
		it = bshit[dind];
  		while (TRUE) /* display as long as there are matches*/
  		{
			srchlen = slencal(dind,fbuff);
  			xjdserver (XJ_ENTRY, DicNum, it, srchlen, 
			fbuff, &xjresp, &respos, &roff, &rlen, repstr, &DicLoc);
/* printf("E: Returning: %d %ld %d %d %ld %s\n",xjresp,respos,roff,rlen,DicLoc,repstr);  */
  			if (xjresp != XJ_OK) break;
			schix =  0;
			schiy = roff;
		/* make copy of line for filter testing   */
			slk=0;
			for(schiz=0;repstr[schiz]>=0x20;schiz++)
			{
				testline[schiz] = repstr[schiz];
				if(testline[schiz]=='/')slk++;
			}
			testline[schiz] = '\0';
			kanj1 = testline[0];
			kanj2 = testline[1];
			FiltOK = TRUE;
		/* now if filters are active, check the line for a match   */
			if((Dmode == 0)&& nofilts && (!GDmode))
			{
				if(nofilts>0)
				{
					for (i=0;i<NOFILT;i++)
					{
						if(!filtact[i]||!filton[i])continue;
						if(filttype[i] == 0)
						{
							FiltOK = FALSE;
							for(j=0;j<filtcoden[i];j++)
							{
								if(strstr(testline,filtcodes[i][j]) != NULL)
								{
									FiltOK = TRUE;
									break;
								}
							}
							if(FiltOK)break;
						}
						if((filttype[i] == 1)||((filttype[i] == 2)&&(slk <= 2)))
						{
							FiltOK = TRUE;
							for(j=0;j<filtcoden[i];j++)
							{
								if(strstr(testline,filtcodes[i][j]) != NULL)
								{
									FiltOK = FALSE;
									break;
								}
							}
								if(!FiltOK) break;
						}
					}
				}
			}
			if(strf && (Dmode ==1))
			{
				FiltOK = FALSE;
				if (strstr(testline,strfilt) != NULL) FiltOK = TRUE;
			}
			if ((Dmode == 0) && SFFlag && FiltOK)
			{
				FiltOK = FALSE;
				kptr = strstr(testline,SingleFilter);
				if ((kptr != NULL) && (SingleFilter[0] < 128))
				{
					FiltOK = TRUE;
				}
				else
				{
					while (TRUE)
					{
						if (kptr == NULL) break;
						if ((strlen(testline) - strlen(kptr)) % 2 == 0)
						{
							FiltOK = TRUE;
							break;
						}
						else
						{
							kptr2 = kptr;
							kptr = strstr(kptr2+1,SingleFilter);
						}
					}
				}
			}
			if ((EMmode == 0) && (((fbuff[0] <127) && isalnum(repstr[roff+srchlenok])) 
				||((fbuff[0] >=0xa4) && (repstr[roff+srchlenok] > 127))))
			{
				FiltOK = FALSE;
			}
			KFlushRes = TRUE;
		/* now work forwards, displaying the line  */
			KTest = TRUE;
			if (((fbuff[0] > 0xa5) || (fbuff[0] == 0x8f)) && (roff != 0)) KTest = FALSE;
			if ((Dmode == 0) && GDmode) KTest = TRUE;
			if (roff != 0) gdiclen--;
			if (FiltOK && addhit(DicLoc) && (!FirstKanj || (FirstKanj && KTest)))
			{
				DispHit = TRUE;
				if ((Dmode == 0) &&(ROmode == 0))
				{
			/* We are in "raw output mode, so just splat out the EDICT line.
			   Note that this block does its own "end-of display" processing */
					for(schiz=0;repstr[schiz]>=0x20;schiz++)
					{
						KLine[schiz] = repstr[schiz];
					}
					KLine[schiz] = '\0';
					KFlushRes = KFlush("Continue displaying matches? (y/n)");
					it++;
					if (!KFlushRes) return;
					continue;
				}
				engrv = FALSE;
				EngFirst = TRUE;
				if((Dmode == 0) || ((Dmode ==1)&&(KLRmode == 0))) KLine[0] = 0;
				if (Dmode == 0)
				{
					if (fbuff[0] == SPTAG)
					{
						sprintf(ops,"%d: ",dind);
						strcpy(KLine,ops);
					}
					else
					{
						sprintf(ops,"%d: ",dind+1);
						strcpy(KLine,ops);
					}
					DCol = 0;
				}
				strcat(KLine," ");
				if (Dmode == 1)
				{
					KDNSflag = TRUE;
					prevch = 0;
					ops[0] = 0xa1; ops[1] = 0xda;
					kanj1 =  repstr[0];
					kanj2 =  repstr[1];
					kanj3 =  repstr[2];
					ops[2] =  repstr[0];
					ops[3] =  repstr[1];
					ops[4] =  repstr[2];
					ops[5] = 0;
					if (ops[2] != 0x8f) ops[4] = 0;
					instr[0] = 0xa1; instr[1] = 0xdb; instr[2] = 0;
					strcat (ops,instr);
					if (KLRmode == 0) 
					{
						if (ops[2] == 0x8f)
						{
							sprintf (instr,"%s 1-%x%x [1-%d]",ops,kanj2&0x7f,kanj3&0x7f,((kanj2&0x7f)-0x20)*100+(kanj3&0x7f)-0x20);
							schix+=8;

						}
						else
						{
							k1 = kanj1 & 0x7f;
							k2 = kanj2 & 0x7f;
							jis2sjis(&k1,&k2);
							sprintf (instr,"%s %x%x [%d:%x%x]",ops,kanj1&0x7f,kanj2&0x7f,((kanj1&0x7f)-0x20)*100+(kanj2&0x7f)-0x20,k1,k2);
							schix+=7;
						}	
						strcat(KLine,instr);
					}
					else
					{
						KLine[0] = 0;
						karray[nok][2] = kanj1;
						karray[nok][3] = kanj2;
						karray[nok][4] = kanj3;
						kptr = strstr(testline,"S");
						if (kptr == NULL)
						{
							karray[nok][0] = 0;
						}
						else
						{
							karray[nok][0] = atoi(kptr+1);
						}
						kptr = strstr(testline,"B");
						if (kptr == NULL)
						{
							karray[nok][1] = 0;
						}
						else
						{
							karray[nok][1] = atoi(kptr+1);
						}
						KLcount++;
						if (nok < KANJARRAYSIZE) nok++;
						continue;
					}
				}
				KDskip = FALSE;
				while ((cc = repstr[schix]) != 0x0a)
				{
					if (cc == 0x0d) break;
					if (RVACTIVE && (schix == roff)) strcat (KLine,RVon);
					if (RVACTIVE && (schix == roff+srchlen)) strcat (KLine,RVoff);
					if ((Dmode == 0) && (cc == '['))
					{
						ops[0] = 0xa1; ops[1] = 0xca; ops[2] = 0; /* JIS (  */
						strcat(KLine,ops);
						schix++;
						continue;
					}
					if ((Dmode == 0) && (cc == ']'))
					{
						ops[0] = 0xa1; ops[1] = 0xcb; ops[2] = 0; /* JIS (  */
						strcat(KLine,ops);
						schix++;
						continue;
					}
					if (KDskip)
					{
						if (cc == ' ')KDskip = FALSE;
						schix++;
						continue;
					}
					if (cc < 128) /* non-Japanese, display it (fix up the EDICT "/") */
					{
						ops[0]= cc;
						ops[1] = '\0';
						if (cc == SPTAG)
						{
							if (prieng)
							{
								strcat (KLine,RVon);
								engrv = TRUE;
							}
							schix++;
							continue;
						}
						if (!isalnum(cc) && engrv)
						{
							engrv = FALSE;
							strcat (KLine,RVoff);
						}
						if (KDNSflag && (prevch == ' ') && (Dmode != 0))
						{
							if (strstr(KDNSlist,ops) != NULL)
							{
								KDskip = TRUE;
								schix++;
								continue;
							}
						}
						prevch = cc;
						if ((Dmode == 1) && (cc == '}'))  /* { */
						{
							ops[0] = ';';
							if ((repstr[schix+2] == 0x0a) && (ops[0] == ';')) ops[0] = '\0';
						}
						if ((Dmode == 1) && (cc == '{')) 
						{
							KDNSflag = FALSE;
							schix++;
							continue;
          				}
						if ((Dmode == 0) && (ops[0] == '/'))
						{
							if (!EngFirst)
							{
								ops[0] = ';';
								ops[1] = ' ';
								ops[2] = 0;
							}
							else
							{
								EngFirst = FALSE;
								ops[0] = 0;
							}
						}
						if ((repstr[schix+1] == 0x0a) && (ops[0] == ';')) ops[0] = '\0';
						if ((repstr[schix+1] == 0x0d) && (ops[0] == ';')) ops[0] = '\0';
						strcat(KLine,ops);
					}
					else   /* kana or kanji  */
					{
						if (cc == 0x8f)
						{
							KOutc(0x8f);
							schix++;
							continue;
						}
						if (khi == 0)
						{
							khi = cc;
						}
						else
						{
							klo = cc;
							KOutc(khi);
							KOutc(klo);
							khi = 0;
						}
					}
					schix++;
				}  /* end of line display loop  */
				if (GDmode && (Dmode == 0)) return;  /* early return from global*/
				if (Dmode == 0) KFlushRes = KFlush("Continue displaying matches? (y/n)");
				if ((Dmode == 1)&&(KLRmode == 0)) KFlushRes = KFlush("Continue displaying matches? (y/n)");
			}  /* of "once-per-line" test */
			it++;
			if ((Dmode == 0)||((Dmode ==1)&&(KLRmode == 0)))
			{
				if (!KFlushRes) return;
			}
		}  /*  end of the "while it matches loop  */
		if (!DispHit) printf("No display for this key (filtered or non-initial kanji)\n");
		if ((Dmode == 1)&&(KLRmode == 1)) 
		{
			if (nok >= KANJARRAYSIZE) printf("\nWarning! Kanji table overflow!\n");
			if (nok == 0) return;

/* Thanks to Bruce Raup for the casting which fixed the compilation
 * warning in the following qsort() call
 */
			qsort(&karray,nok,sizeof(karray[0]),(int (*) (const void *, const void *)) kcmp);
			for (i = 0; i < nok; i++)
			{
				if ((i != 0) && (karray[i][2] == karray[i-1][2]) && (karray[i][3] == karray[i-1][3]) && (karray[i][4] == karray[i-1][4])) continue;
				KOutc(karray[i][2]);
				KOutc(karray[i][3]);
				if (karray[i][2] == 0x8f) KOutc(karray[i][4]);
				KOutc(' ');
			}
			KFlushRes = KFlush("Continue displaying kanji (y/n)");
		}
		if ((Dmode != 0) || (dind == 0)) return;
		if (EMmode == 0) return;
		printf("End of %d character matches. Continue for shorter matches? (y/n)\n\r",dind+1);
		ops[0] = getcharxx();
		DRow = 1;
		fflush(stdin);
		if ((ops[0] == 'y')||(ops[0] == 'Y')) continue;
		if ((ops[0] != 'n')&&(ops[0] != 'N')) 
		{
			if ((ops[0] != 0x0a) && (ops[0] != 0x0d)) ungetc(ops[0],stdin);
		}
		break;
	}  /* end of the dind loop  */
}  /* end of lookup */

/*======RadSet=== set up Radicals for bushu search=================*/
void RadSet()
{
	int i,errf;
	unsigned char rstr[20];
	FILE *fpr, *fopen();

	fpr = xfopen(Rname,"r", &xfilelen);
	i = 0;
	while(TRUE)
	{
		errf = (fgets(rstr,19,fpr) == NULL);
		if (feof(fpr)||errf) break;
		while(rstr[strlen(rstr)-1] < 0x20) rstr[strlen(rstr)-1] = 0;
		if (rstr[3]  == '0') continue;
		radkanj[i][0] = rstr[0];
		radkanj[i][1] = rstr[1];
		if (rstr[3] == '(')
		{
			radnos[i] = atoi(rstr+4);
		}
		else
		{
			radnos[i] = atoi(rstr+3);
		}
		i++;
	}
	fclose(fpr);
	return;
}
/*=====DispLic======display GPL ==============================*/
void DispLic()
{
	FILE *flic,*fopen();

	flic = xfopen(GPL_File,"r", &xfilelen);
	DRow = 1;
	DCol = 0;
	while (!feof(flic))
	{
		fgets(KLine,81,flic);
		if (feof(flic))
		{
			KFlush("");
			return;
		}
		KLine[strlen(KLine)-1] = 0;
		if(!KFlush("Continue Licence Display? (y/n)")) return;
	}
}
/*=====DoRADICALS===display Theresa's Radical File================*/

void DoRADICALS()
{

	int errf,j;
	unsigned char rstr[20];
	FILE *fpr, *fopen();

	fpr = xfopen(Rname,"r", &xfilelen);
	printf("\n RADICAL DISPLAY \n");
	DRow = 3;
	DCol = 0;
	KLine[0] = 0;
	fseek(stdin,0L,SEEK_END); /*kill any leftovers*/
	j = 0;
	while(TRUE)
	{
		errf = (fgets(rstr,19,fpr) == NULL);
		if (feof(fpr)||errf)
		{
			KFlush("");
			fseek(stdin,0L,SEEK_END); /*kill any leftovers*/
			return;
		}
		while(rstr[strlen(rstr)-1] < 0x20) rstr[strlen(rstr)-1] = 0;
		if ((rstr[strlen(rstr)-2]  == ' ')&&(rstr[strlen(rstr)-1]  == '0'))
		{
			KFlushRes = KFlush("Continue displaying radicals? (y/n)");
			if (!KFlushRes) return;
			strcpy(KLine,"  ");
			KFlushRes = KFlush("Continue displaying radicals? (y/n)");
			if (!KFlushRes) return;
			rstr[2] = 0;
			sprintf(tempout,"%s Stroke Radicals ",rstr);
			strcpy(KLine,tempout);
			KFlushRes = KFlush("Continue displaying radicals? (y/n)");
			if (!KFlushRes) return;
			strcpy(KLine,"  ");
			KFlushRes = KFlush("Continue displaying radicals? (y/n)");
			if (!KFlushRes) return;
			continue;
		}
		strcat(KLine,"\t");
		KOutc(rstr[0]);
		KOutc(rstr[1]);
		KOutc(0xa1);
		KOutc(0xa1);
		sprintf(tempout,"%s ",rstr+3);
		strcat(KLine,tempout);
	}
	KFlush("");
}

/*=========KLookup=== Special front-end to Lookup for Kanji searches==========*/
void KLookup()
{
	if (KLmode == 0)	/* Long display mode, just pass on call  */
	{
		KLRmode = 0;
		Lookup();
		return;
	}			/* Short display mode - see how many there */
	KLRmode = 1;
	Lookup();
	if (KLcount == 1)	/* only one - force long display	*/
	{
		KLRmode = 0;
		Lookup();
	}
	return;
}

/*=========DoJIS === JIS kanji lookup==========================================*/

void DoJIS()
{
	int i,ktf,sjf,hojof,i1,i2;
	unsigned char cj;

	ktf = FALSE;
	sjf = FALSE;
	hojof = FALSE;
	cbreakoff();
	scanf("%s",instr);
	cbreakon();
	fflush(stdin);
	cj = instr[0];
	if ((cj == '-') || (cj == 'k') || (cj == 'K'))
	{
		ktf = TRUE;
		strcpy(instr,instr+1);
	}
	else if ((cj == 's')||(cj == 'S'))
	{
		sjf = TRUE;
		strcpy(instr,instr+1);
	}
	cj = instr[0];
	if ((cj == 'h') || (cj == 'H'))
	{
		hojof = TRUE;
		strcpy(instr,instr+1);
	}
	if (ktf)
	{
		for (i = 0;i <4; i++)
		{
			if ((instr[i] >= '0') && (instr[i] <= '9'))instr[i] = instr[i] - '0';
		}
		instr[0] = (instr[0]*10+instr[1]+0x20) | 0x80;
		instr[1] = (instr[2]*10+instr[3]+0x20) | 0x80;
		instr[2] = 0;
	}
	else
	{
		for (i = 0;i <4; i++)
		{
			if ((instr[i] >= '0') && (instr[i] <= '9'))instr[i] = instr[i] - '0';
			if ((instr[i] >= 'a') && (instr[i] <= 'f'))instr[i] = instr[i]-'a'+0x0a;
			if ((instr[i] >= 'A') && (instr[i] <= 'F'))instr[i] = instr[i]-'A'+0x0a;
		}
		if(sjf)
		{
			i1 = (instr[0] << 4) + instr[1];
			i2 = (instr[2] << 4) + instr[3];
			sjis2jis(&i1,&i2);
			instr[0] = i1 | 0x80;
			instr[1] = i2 | 0x80;
			instr[2] = 0;
		}
		else
		{
			instr[0] = ((instr[0] << 4) + instr[1]) | 0x80;
			instr[1] = ((instr[2] << 4) + instr[3]) | 0x80;
			instr[2] = 0;
		}
	}
	Dmode =1;
	fbuff[0] = 0; fbuff[1] = 0;
	if (hojof) fbuff[0] = 0x8f;
	strcat(fbuff,instr);
	fseek(stdin,0L,SEEK_END); /*kill any leftovers*/
	KLookup();
	instr[0] = 0;
}

/*=====  GetKBStr=== Collect ASCII or JIS string from keyboard=========*/

void GetKBStr(unsigned char *prompt)
{
	int ShowIt,escf,bit8,i;
	unsigned char c;

	escf = FALSE;
	bit8 = FALSE;
	c='x'; /*keep lint happy*/
	ShowIt = FALSE;

	for (i = 0; (c != 0xd) && (c != 0xa); i++)
	{
		instr[i+1] = 0;
		c = getcharxx();
		if (!bit8 && !escf && ((c == '@') || (c == '#')))
		{
			DoRomaji(c);
			break;
		}
		if (c == 0x1b) escf = TRUE;
		if (c > 0x7f) bit8 = TRUE;
		if ((c == 0x7f) || (c == 8))
		{
			if(bit8) i--;
			if( i > 0) instr[--i] = 0;
			i--;
			strcpy(fbuff,instr);
			if (!NoSJIS) FixSJIS(fbuff);
			printf("\r                                       \r");
			printf("%s%s%s ",RVon,prompt,RVoff);
			KOut(fbuff);
			continue;
		}
		instr[i] = c;
		if (!escf)
		{
			if (!bit8)
			{
				printf("\r                                       \r");
				printf("%s%s%s %s",RVon,prompt,RVoff,instr);
			}
			else
			{
				strcpy(fbuff,instr);
				if ((strlen(fbuff) % 2) > 0) fbuff[strlen(fbuff)-1] = 0;
				printf("\r                                       \r");
				printf("%s%s%s ",RVon,prompt,RVoff);
				if (!NoSJIS) FixSJIS(fbuff);
				KOut(fbuff);
			}
		}
		if ((instr[i] == 'B')&&(instr[i-1] == '(')&&(instr[i-2] == 0x1b)) 
		{
			ShowIt = TRUE;
			break;
		}
	}
	fseek(stdin,0L,SEEK_END); /*kill any leftovers*/
	fflush(stdin);
	GetEUC(fbuff);
	if ( fbuff[strlen(fbuff)-1] < 0x20) fbuff[strlen(fbuff)-1] = 0;
	if (ShowIt)
	{
		printf("\r                                       \r");
		printf("%s%s%s ",RVon,prompt,RVoff);
		KOut(fbuff);
	}
	printf("\n\r");
}

/*=====  OneShot === Collect and set single filter=============*/

void OneShot()
{
	printf("\nFilter inactivated. Enter new filter, or press return\n\n");
	printf("%sFILTER:%s ",RVon,RVoff);
        SFFlag = FALSE;

	GetKBStr("FILTER:");
	strcpy(SingleFilter,fbuff);
	if (strlen(fbuff) >= 2) 
	{
		SFFlag = TRUE;
		printf("Filter set to: ");
		KOut(fbuff);
		printf("\n");
	}
	else
	{
		printf("No filter set\n");
	}
}

/*====FindRad=== finds the spot in the table for a radical==========*/
int FindRad(unsigned char char1, unsigned char char2)
{
	int i,j,k,Found;

	Found = FALSE;
	for (i = 0; i <= NoRads; i++)
	{
		if ((char1 == RadK1[i]) && (char2 == RadK2[i]))
		{
			Found = TRUE;
			break;
		}
	}
	if (!Found) return(-1);
	return(i);
}
/*===RadBuild==Extracts the kanji that meet the multi-radical selection===*/
void RadBuild()
{
/*	RKTarg will contain the string of target "radicals"
	The RKSet tables are progressively loaded with the kanji that 
	meet the radical criteria		*/

	int stest,jtest,i,j,k,l,m,n,lind,hitcount;

/*	the first radical has all its kanji loaded (which meet any stroke count test)	*/
	i = FindRad((unsigned char)RKTarg[0],(unsigned char)RKTarg[1]);
	if (i < 0)
	{
		printf("Invalid Radical!\n");
		RKTarg[0] = 0;
		return;
	}
	k = 0;
	hitcount = 0;
	for (j = RKStart[i]; j < RKStart[i]+RKCnt[i]; j++)
	{
		if (kstrokelim > 0)
		{
			n = ((RKanj1[j] & 0x7f)-0x30)*94 + ((RKanj2[j] & 0x7f) - 0x21);
			if ((kstroketype == 0) && (kstrokelim != kstrokes[n])) continue;
			if ((kstroketype == 1) && (kstrokelim > kstrokes[n])) continue;
			if ((kstroketype == 2) && (kstrokelim < kstrokes[n])) continue;
		}
		RKSet[0][k] = RKanj1[j];
		RKSet[0][k+1] = RKanj2[j];
		RKSet[0][k+2] = 0;
		hitcount++;
		k+=2;
	}
	ops[0] = RKTarg[0]; ops[1] = RKTarg[1]; ops[2] = 0;
	printf("Target Radicals: 0 ");
	KOut(ops);
	printf(" (%d) ",hitcount);
	NoSets = 1;
	if (strlen(RKTarg) <= 2)
	{
		printf("\n");
		return;
	}
/* The second and subsequent radicals only have their matching kanji loaded
	if they are a member of the previous set		*/

	for (l=2; l< strlen(RKTarg); l+=2)
	{
		lind = (l/2)-1;
		i = FindRad((unsigned char)RKTarg[l],(unsigned char)RKTarg[l+1]);
		ops[0] = RKTarg[l]; ops[1] = RKTarg[l+1]; ops[2] = 0;
		printf(" %d ",NoSets);
		KOut(ops);
		if (i < 0)
		{
			printf("\nInvalid Radical!\n");
			RKTarg[l] = 0;
			return;
		}
		k = 0;
		RKSet[lind+1][k] = 0;
		jtest = RKStart[i]+RKCnt[i];
		for (j = RKStart[i]; j < jtest; j++)
		{
			for (n = 0; RKSet[lind][n] != 0; n+=2)
			{
				if ((RKSet[lind][n] == RKanj1[j]) && (RKSet[lind][n+1] == RKanj2[j]))
				{
					RKSet[lind+1][k] = RKanj1[j];
					RKSet[lind+1][k+1] = RKanj2[j];
					RKSet[lind+1][k+2] = 0;
					k+=2;
					break;
				}
			}
		}
		NoSets++;
		printf(" (%d) ",strlen(RKSet[NoSets-1])/2);
	}
	printf("\n");
}

/*=====RadDisp===Display Radical Data==============================*/
void RadDisp()
{
	FILE *fk,*fopen();
	int j,k,l,n;
	unsigned char *ptr;

	fk = xfopen(RKname,"r", &xfilelen);
	j = 0;
	printf("RADICAL TABLE FOR USE WITH THE XJDIC RADICAL LOOKUP FUNCTION\n");
	DRow = 0;
	DCol = 0;
	k = 99;
	KLine[0] = 0;
	while(!feof(fk))
	{
		fgets(testline,199,fk);
		if(feof(fk)) break;
		if (testline[0] != '$') continue;
		ptr = strtok(testline+4," ");
		l = atoi(ptr);
		if (l != k)
		{
			k = l;
			for (n = 0; n < strlen(ptr); n++)
			{
				if (ptr[n] < 32) break;
				KOutc(0xa3); KOutc(ptr[n] | 0x80);
			}
			KOutc(' ');
		}
		KOutc(testline[2]); KOutc(testline[3]); KOutc(' ');
	}
	fclose(fk);
	KFlush("");
}
/*===KanjRad=== Display which "radicals" are used to imdex this kanji=====*/
void KanjRad()
{
	int i,j;

	printf("%sWhich Kanji:%s",RVon,RVoff);
	GetKBStr("Which Kanji:");
	if (fbuff[0] < 127) return;
	strcpy(KLine,"Kanji: ");
	KOutc(fbuff[0]);
	KOutc(fbuff[1]);
	strcat(KLine," Elements: ");
	DRow = 0;
	DCol = 0;
	for (i = 0; i <= NoRads; i++)
	{
		for (j = RKStart[i]; j < RKStart[i]+RKCnt[i]; j++)
		{
			if ((fbuff[0] == RKanj1[j]) && (fbuff[1] == RKanj2[j]))
			{
				KOutc(RadK1[i]);
				KOutc(RadK2[i]);
				KOutc(' ');
			}
		}
	}
	KFlush("");
}
/*====RadKDisp=====display selected kanji============================*/
void RadKDisp()
{
	int i;

	if (RKTarg[0] == 0) return;
	if (NoSets == 0) return;
	printf("Selected Kanji: ");
	for (i = 0; i < strlen(RKSet[NoSets-1]); i+=2)
	{
		ops[0] = RKSet[NoSets-1][i]; ops[1] = RKSet[NoSets-1][i+1]; ops[2] = 0;
		KOut(ops);
		printf(" ");
	}
	printf("\n");
}
/*====DoLOOKUP=====driver routine for the multi-radical lookup=======*/
void DoLOOKUP()
{
	int i;

	printf("\nRadical Lookup Mode\n");
	RKTarg[0] = 0;
	while(TRUE)
	{
		printf("%sLookup Code:%s",RVon,RVoff);
		GetKBStr("Lookup Code:");
		if (fbuff[0] > 127)
		{
			ops[0] = fbuff[0]; ops[1] = fbuff[1]; ops[2] = 0;
			if (strlen(RKTarg) == 20)
			{
				printf("\nToo many radicals!\n");
				continue;
			}
			strcat(RKTarg,ops);
			RadBuild();
			if(NoSets == 0) continue;
			if (strlen(RKSet[NoSets-1]) == 0) continue;
			if (strlen(RKSet[NoSets-1]) <=RADLOOKLIM) RadKDisp();
			continue;
		}
		if ((fbuff[0] | 0x20) == 'r')
		{
			RadDisp();
			continue;
		}
		if ((fbuff[0] | 0x20) == 'v')
		{
			KanjRad();
			continue;
		}
		if ((fbuff[0] | 0x20) == 'x')
		{
			instr[0] = 0;
			fflush(stdin);
			return;
		}
		if ((fbuff[0] | 0x20) == 'c')
		{
			RKTarg[0] = 0;
			kstrokelim = 0;
			printf("Cleared\n");
			continue;
		}
		if ((fbuff[0] | 0x20) == 's')
		{
			kstroketype = 0;
			i = 1;
			testline[0] = 0;
			if (fbuff[1] == '+') 
			{
				kstroketype = 1;
				strcat(testline," >= ");
				i = 2;
			}
			if (fbuff[1] == '-') 
			{
				kstroketype = 2;
				strcat(testline," <= ");
				i = 2;
			}
			kstrokelim = atoi(fbuff+i);
			if (kstrokelim == 0)
			{
				printf("Stroke-count cleared\n");
			}
			else
			{
				printf("Stroke-count set to %s%d\n",testline,kstrokelim);
			}
			if (strlen(RKTarg) > 0) RadBuild();
			if (NoSets <= 0) continue;
			if (strlen(RKSet[NoSets-1]) <=RADLOOKLIM) RadKDisp();
			continue;
		}
		if ((fbuff[0] | 0x20) == 'd')
		{
			i = fbuff[1]-'0';
			if (i >= strlen(RKTarg)/2)
			{
				printf("Out of Range!\n");
				continue;
			}
			strcpy(RKTarg+i*2,RKTarg+i*2+2);
			if(strlen(RKTarg) > 0) RadBuild();
			if (strlen(RKSet[NoSets-1]) <=RADLOOKLIM) RadKDisp();
			continue;
		}

		if ((fbuff[0] | 0x20) == 'l') RadKDisp();
	}
}

/*=====  DoKANJI === Kanji single lookup ======================*/
void DoKANJI()
{

	GetKBStr("KANJI/KANA:");
	Dmode =1;
	KLookup();
	instr[0] = 0;
}
/*===EMtoggle==alternate between match display  modes===============*/
void EMtoggle()
{
	EMmode = (EMmode+1) % 2;
	printf("Exact Match Display Mode: %s\n",kmodes[EMmode]);
}
/*===togglekana==alternate between kana input modes===============*/
void togglekana()
{
	KImode = (KImode+1) % 2;
	printf("Kana Default Input Mode: %s\n",kmodes[KImode]);
}
/*===togglekanji==alternate between kanji display  modes===============*/
void togglekanji()
{
	KLmode = (KLmode+1) % 2;
	printf("Long Kanji Display Mode: %s\n",kmodes[KLmode]);
}
/*===toggleraw===alternate between raw/edited output modes===============*/
void toggleraw()
{
	ROmode = (ROmode+1) % 2;
	printf("Unedited Output Mode: %s\n",kmodes[ROmode]);
}
/*===RVtoggle===alternate between reverse video modes===============*/
void RVtoggle()
{
	RVACTIVE  = (RVACTIVE +1) % 2;
	printf("Reverse Video Match Display Mode: %s\n",kmodes_r[RVACTIVE ]);
}
/*===togglemode===alternate between kanji compound modes===============*/
void togglemode()
{
	FirstKanj = (FirstKanj+1) % 2;
	printf("Display All Kanji Mode: %s\n",kmodes[FirstKanj]);
}

/*=====engpritoggle=====alternate between English priorities=======*/
void engpritoggle()
{
	if(prieng == FALSE)
	{
		prieng = TRUE;
		printf("English search will now only select priority keys\n");
		return;
	}
	prieng = FALSE;
	printf("English search will now select all keys\n");
}

/*=====seldic=====select dictionary file =====================*/
void seldic()
{
	int i;
	char c;

	if (NoDics == 1)
	{
		printf("No alternative dictionary active!\n");
		return;
	}
	for (i = 1; i <= NoDics; i++)
	{
		printf("Dictionary: %d  [%s]\n",i,DicName(i));
	}
	printf ("Select a dictionary file (1-%d)\n",NoDics);
	c = getcharxx();
	if ((c ==  0x1b)||(c == 0xa)||(c == 0xd)) return;
	i = c-'0';
	if ((i <0)||(i >NoDics))
	{
		printf("INVALID!\n");
		return;
	}
	CurrDic = i;
	printf("Active Dictionary is now #%d (%s)\n",CurrDic,DicName(CurrDic));
}

/*=====BuffStats=====report on page buffer stats=====================*/
void BuffStats()
{
	int i;

#ifdef XJDDIC
	printf("DEMAND-PAGING STATISTICS:\n\n");
	printf("Dic Hits: ");
	for (i=0;i<=NoDics;i++) printf("\t%ld ",dichits[i]);
	printf("\n");
	printf("Dic Miss: ");
	for (i=0;i<=NoDics;i++) printf("\t%ld ",dicmiss[i]);
	printf("\n");
	printf("Ind Hits: ");
	for (i=0;i<=NoDics;i++) printf("\t%ld ",indhits[i]);
	printf("\n");
	printf("Ind Miss: ");
	for (i=0;i<=NoDics;i++) printf("\t%ld ",indmiss[i]);
	printf("\n");
	printf("Buffer overwrites: \t%ld\n",vbkills);
#else
	printf("CLIENT! NO BUFFER STATISTICS\n");
#endif
}
/*=====altdic=====rotate around dictionaries=======*/
void altdic(int dicincr)
{
	if (NoDics == 1)
	{
		printf("No alternative dictionary active!\n");
		return;
	}
	CurrDic = CurrDic + dicincr;
	if (CurrDic == NoDics+1) CurrDic = 1;
	if (CurrDic == 0) CurrDic = NoDics;
	printf("Switching to dictionary: %d [%s]\n",CurrDic,DicName(CurrDic));
}
/*====GDicSet====== initialize the global dictionary list===============*/
void  GDicSet()
{
	char gdtemp[100],*gdp;

	if (NoDics == 1)
	{
		printf("No alternative dictionary active!\n");
		return;
	}

	gdicmax = 0;
	printf("\nEnter the list of dictionary numbers for the global search\n");
	printf("%sDictionary Numbers:%s",RVon,RVoff);
	GetKBStr("Dictionary Numbers:");
	strcpy(gdtemp,fbuff);
	gdp = strtok(gdtemp," ,\t");
	while(gdp!=NULL)
	{
		gdicnos[gdicmax] = atoi(gdp);
		gdp = strtok(NULL," ,\t");
		gdicmax++;
		if (gdicmax > 9)
		{
			printf("Too many dictionary numbers!\n");
			gdicmax--;
			break;
		}
		if (gdicnos[gdicmax-1] > NoDics)
		{
			printf("Illegal Dictionary number!\n");
			gdicmax--;
		}
	}
	gdicmax--;
	if (gdicmax <1)
	{
		printf("Warning! Insufficient dictionaries set!\n");
	}
}

/*====GDictoggle=== alternate between single & global dics==============*/
void GDictoggle()
{
	int gi;

	if (GDmode)
	{
		GDmode = FALSE;
		printf("Global dictionary searching is now OFF\n");
	}
	else
	{
		if (gdicmax <1)
		{
			printf("Insufficient dictionaries set!\n");
			return;
		}
		GDmode = TRUE; 
		printf("Global dictionary searching is now ON [");
		for (gi=0;gi<=gdicmax;gi++)
		{
			printf("%d",gdicnos[gi]);
			if (gi != gdicmax) printf(" ");
		}
		printf("]\n");
	}
}
/*====GDicALLtoggle=== alternate between single & multiple global dic  disp====*/
void GDicALLtoggle()
{
	if(GDALLmode)
	{
		GDALLmode = FALSE;
		printf("Multiple Global Display is now OFF\n");
	}
	else
	{
		GDALLmode = TRUE;
		printf("Multiple Global Display is now ON\n");
	}
}
/*====Verbtoggle=== alternate between deinflection on/off===============*/
void Verbtoggle()
{
	if (Jverb)
	{
		Jverb = FALSE;
		printf("Verb deinflection is now OFF\n");
	}
	else
	{
		Jverb = TRUE; 
		printf("Verb deinflection is now ON\n");
	}
}
/*=== FiltSet=== turn filters on & off==============================*/
void FiltSet()
{
	unsigned char c,fff[10];
	int anyfilt,j,k;

	anyfilt = FALSE;
	printf("%sFilter Setting%s\n",RVon,RVoff);
	for(j = 0;j < NOFILT;j++)
	{
		if(!filtact[j])continue;
		anyfilt = TRUE;
		strcpy(fff,"OFF");
		if(filton[j])strcpy(fff,"ON ");
		printf("No: %d Type: %d Status: %s Name: %s\n",j,filttype[j],fff,filtnames[j]);
	}
	if (!anyfilt)
	{
		printf("No filters are loaded!\n");
		return;
	}
	printf("Modify which Filter?\n");
	c = getcharxx();
	if ((c ==  0x1b)||(c == 0xa)||(c == 0xd)) return;
	k = c-'0';
	if ((k <0)||(k >NOFILT))
	{
		printf("INVALID!\n");
		return;
	}
	if (!filtact[k])
	{
		printf("Filter %c is not active!\n",c);
		return;
	}
	printf("Filter %c OFF (0) or ON (1)\n",c);
	c = getcharxx();
	if ((c != '0') && (c != '1'))return;
	if(c == '0') 
	{
		filton[k] = FALSE;
		printf("Filter %d Turned OFF\n",k);
	}
	if(c == '1')
	{
		filton[k] = TRUE;
		printf("Filter %d Turned ON\n",k);
	}
	nofilts = FALSE;
	for(j = 0;j < NOFILT;j++)if(filton[j])nofilts=TRUE;
	return;
}

/*                  M A I N                                      */

main(argc,argv)
int argc;
unsigned char **argv;

{
	int i,j,ip,cmdmode,bit8,escf;
  	unsigned char *dicenv,strtmp[50];
  	unsigned char c;
	unsigned char xap[50];
	unsigned char kbprompt[99];
	unsigned char kbprompt2[99];
	
  	printf("XJDIC Version %s (Japanese Dictionary) Copyright J.W.Breen 2003.\n",sver);
#ifdef XJDDIC
	printf("   Stand-alone mode\n");
#else
	printf("   Client mode\n");
#endif

	for (i=0;i<NOFILT;i++)
	{
		filtact[i] = FALSE;
		filton[i] = FALSE;
	}
	dicenv = (unsigned char *)getenv("XJDIC");
	if (!dicenv) dicenv = (unsigned char *)DEFAULT_DICDIR;
	if (strlen(dicenv) <= 2) 
	{
		dicenv = (unsigned char *)getcwd(ENVname,sizeof(ENVname));
		if (dicenv == NULL) 
		{
			printf("Cannot extract working directory!\n");
			exit(1);
		}
	}
	else
	{
		strcpy (ENVname,dicenv);
        }
#ifdef XJDDIC
        strcpy (Dnamet[1],"edict");
        strcpy (Dnamet[0], "kanjidic");
        strcpy (XJDXnamet[1], "edict.xjdx");
        strcpy (XJDXnamet[0], "kanjidic.xjdx");
	NoDics = 1;
	CurrDic = 1;
#endif
	cl_rcfile[0] = 0;
/* process command-line options*/
	if (argc > 1)
	{
		for (i = 1; i < argc; i++)
		{
			strcpy(xap,argv[i]);
			if ((xap[0] == '-') && (xap[1] == 'c'))
			{
				if(xap[2] != 0)
				{
					strcpy(strtmp,xap+2);
				}
				else
				{
					i++;
					strcpy(xap,argv[i]);
					strcpy (strtmp,xap);
				}
				strcpy (cl_rcfile,strtmp);
				printf ("Using control-file: %s\n",cl_rcfile);
			}
			if ((xap[0] == '-') && (xap[1] == 'j'))
			{
				if(xap[2] != 0)
				{
					strcpy(strtmp,xap+2);
				}
				else
				{
					i++;
					strcpy(xap,argv[i]);
					strcpy (strtmp,xap);
				}
				if (strtmp[0] == 'j')
				{
					Omode = 0;
					printf("Output mode set to JIS\n");
				}
				if (strtmp[0] == 's')
				{
					Omode = 2;
					printf("Output mode set to Shift-JIS\n");
				}
				if (strtmp[0] == 'e')
				{
					Omode = 1;
					printf("Output mode set to EUC\n");
				}
				continue;
			}
#ifdef XJDCLSERV
			if ((xap[0] == '-') && (xap[1] == 'S'))
			{
				if(xap[2] != 0)
				{
					strcpy(host,xap+2);
				}
				else
				{
					i++;
					strcpy(xap,argv[i]);
					strcpy(host,xap);
				}
				printf("Command-line request to use server: %s\n",host);
				continue;
			}
			if ((xap[0] == '-') && (xap[1] == 'P'))
			{
				if(xap[2] != 0)
				{
					portno = atoi(xap+2);
				}
				else
				{
					i++;
					strcpy(xap,argv[i]);
					portno = atoi(xap);
				}
				printf("Command-line request to use port: %d\n",portno);
				continue;
			}
#endif
#ifdef XJDDIC
			if ((xap[0] == '-') && (xap[1] == 'C'))
			{
				if(xap[2] != 0)
				{
					strcpy(strtmp,xap+2);
				}
				else
				{
					i++;
					strcpy(xap,argv[i]);
					strcpy (strtmp,xap);
				}
				strcpy (Clip_File,strtmp);
				printf ("Using clipboard-file: %s\n",Clip_File);
			}
			if ((xap[0] == '-') && (xap[1] == 'd'))
			{
				if (thisdic == 0)
				{
					thisdic = 1;
				}
				else
				{
					thisdic++;
					NoDics++;
				}
				if(xap[2] != 0)
				{
					strcpy(strtmp,xap+2);
				}
				else
				{
					i++;
					strcpy(xap,argv[i]);
					strcpy (strtmp,xap);
				}
				strcpy (Dnamet[thisdic],strtmp);
				strcpy (XJDXnamet[thisdic],strtmp);
				strcat (XJDXnamet[thisdic],".xjdx");
				printf("Command-line request to use dictionary files (%d): %s and %s\n",
					thisdic,Dnamet[thisdic],XJDXnamet[thisdic]);
				continue;
			}
			if ((xap[0] == '-') && (xap[1] == 'k'))
			{
				if(xap[2] != 0)
				{
					strcpy(strtmp,xap+2);
				}
				else
				{
					i++;
					strcpy(xap,argv[i]);
					strcpy (strtmp,xap);
				}
				strcpy (Dnamet[0],strtmp);
				strcpy (XJDXnamet[0],strtmp);
				strcat (XJDXnamet[0],".xjdx");
				printf("Command-line request to use kanji dictionary files: %s and %s\n",Dnamet[0],XJDXnamet[0]);
				continue;
			}
#endif
			if ((xap[0] == '-') && (xap[1] == 'V'))
			{
				RVACTIVE = FALSE;
				printf("Reverse-video match display disabled\n");
			}
			if ((xap[0] == '-') && (xap[1] == 'E'))
			{
				NoSJIS = TRUE;
				printf("EUC (No Shift-JIS) operation enforced\n");
			}
			if ((xap[0] == '-') && (xap[1] == 'v'))
			{
				Jverb = FALSE;
				printf("Verb deinflection turned OFF\n");
			}
			if ((xap[0] == '-') && (xap[1] == 'h'))
			{
printf("\nUSAGE: xjdic <options>\n\nwhere options are:\n\n");
printf("   -h this information\n");
printf("   -c control-file\n");
#ifdef XJDCLSERV
printf("   -P port-no\n");
printf("   -S server\n");
#else
printf("   -d dictionary file_path\n");
printf("   -k kanji-dictionary file_path\n");
#endif
printf("   -v disable verb function\n");
printf("   -j x (where x is Output code: e = EUC, s = Shift-JIS, j  = JIS)\n");
printf("   -V disable reverse video display\n");
printf("   -C clipboard-file\n");
printf("\nSee xjdic24.inf for full information\n");
exit(0);
			}
		}
	}
	xjdicrc();
#ifdef XJDDIC
  	printf ("Loading Dictionary and Index files.  Please wait...\n");
#endif
	Verbinit();
  	DicSet ();
	RadSet();
	RadLoad();
	KSLoad();
	LoadKana();
	togglemode();
	togglekanji();
	cbreakon();
	printf("\n(Enter ? for a summary of operating instructions)\n");

/*
	From here on, the code loops endlessly, reading commands 
	from the keyboard. This code decodes any kana/kanji/romaji
	itself, rather than using the "GetKBStr" function, as it has
	to sort out special commands as well.
*/
  	while (TRUE)
	{
		GetWinSize(); /* Just in case the screen has changed  */
		sprintf(kbprompt,"%sXJDIC [%d:%s] SEARCH KEY:%s ",RVon,CurrDic,DicName(CurrDic),RVoff);
		sprintf(kbprompt2,"XJDIC [%d:%s] SEARCH KEY: ",CurrDic,DicName(CurrDic));
		if (GDmode)
		{
			sprintf(kbprompt,"%sXJDIC [GLOBAL] SEARCH KEY:%s ",RVon,RVoff);
			sprintf(kbprompt2,"XJDIC [GLOBAL] SEARCH KEY: ");
		}
		printf("\n\r%s",kbprompt);
		c = 0;
		cmdmode = FALSE;
		strf = FALSE;
		escf = FALSE;
		bit8 = FALSE;
		AKanaMode = FALSE;
		if (KImode == 0) AKanaMode = TRUE;
		for (i = 0; (c != 0xd) && (c != 0xa); i++)
		{
			instr[i+1] = 0;
			if (clipmode) break;
			c = getcharxx();
			if (c == 0x1b) 
			{
				escf = TRUE;
				AKanaMode = FALSE;
			}
			if (c > 0x7f) 
			{
				bit8 = TRUE;
				AKanaMode = FALSE;
			}
			if (!bit8 && !escf && (c == 0x04))   /* Simulate ^D */
			{
				cbreakoff();
				exit(0);
			}
			if (!bit8 && !escf && (c == 0x1a))   /* Simulate ^Z */
			{
				cbreakoff();
				printf("\nSuspending XJDIC. Type `fg' to resume.\n");
				pid = getpid();
				kill(pid,sig);
				cbreakon();
				break;
			}
			/*   Romaji Input	*/
			if (!bit8 && !escf && ((c == '@') || (c == '#')))
			{
				DoRomaji(c);
				break;
			}
			/* On-line Help Summmary		*/
			if ((c == '?') && (!escf) && (!bit8))
			{
				DRow = 0;
				for (ip = 0; strcmp(Help[ip],"$$$")!=0;ip++) 
				{
					strcpy(KLine,Help[ip]);
					if(!KFlush("Continue Help Display? (y/n)")) break;
				}
				break;
			}
			/* Turn on cmd mode for special characters */
			if ((!escf) && (!bit8) && (strchr("!{}$%*&^=/-:\'+\\;][|_`",c) != NULL))
			{
				cmdmode = TRUE; 
				break;
			}
			/* backspace or rubout - shrink i/p buffer and redisplay	*/
			if ((c == 0x7f) || (c == 8))
			{
				if(bit8) i--;
				if( i > 0) instr[--i] = 0;
				i--;
				strcpy(fbuff,instr);
				if (!NoSJIS) FixSJIS(fbuff);
				printf("\r                                       \r");
				printf("%s",kbprompt);
				KOut(fbuff);
				continue;
			}
			/* Actually an input character	*/
			instr[i] = c;
			if (AKanaMode)
			{
				if ((c == 'l') || (c == 'L'))
				{
					AKanaMode = FALSE;
					GetKBStr(kbprompt2);
					break;
				}
				if (c < 128)
				{
					ungetc(c,stdin);
					DoRomaji('@');
					break;
				}
			}
			if (!escf)
			{
				if (!bit8)
				{
					printf("\r					 \r");
					printf("%s%s",kbprompt,instr);
				}
				else
				{
					strcpy(fbuff,instr);
					if ((strlen(fbuff) % 2) > 0) fbuff[strlen(fbuff)-1] = 0;
					printf("\r					 \r");
					printf("%s",kbprompt);
					if (!NoSJIS) FixSJIS(fbuff);
					KOut(fbuff);
				}
			}
			/* JIS ShiftOUT, so terminate input		*/
			if ((instr[i] == 'B')&&(instr[i-1] == '(')&&(instr[i-2] == 0x1b)) break;
		}
		fseek(stdin,0L,SEEK_END); /*kill any leftovers*/
		/* "bye" is the end of the run			*/
		if ((instr[2] == 'e')&&(instr[1] == 'y')&&(instr[0] == 'b')) 
		{
			cbreakoff();
			exit(0);
		}
		/* sort out the special commands		*/
		if(cmdmode)
		{
			if (c == '{')   /* } to balance {}  */
			{
				printf("\r                                    \r");
				printf("Now in Clipboard Mode\n");
				clipmode = TRUE;
				continue;
			}
			if (c == '}')   /* matching {  */
			{
				printf("\r                                      \r");
				RVtoggle();
				continue;
			}
			if (c == '/')
			{
				printf("\r                                      \r");
				togglemode();
				continue;
			}
			if (c == '!')
			{
				printf("\r                                      \r");
				DispLic();
				continue;
			}
			if (c == '|')
			{
				printf("\r                                      \r");
				toggleraw();
				continue;
			}
			if (c == '+')
			{
				printf("\r                                      \r");
				engpritoggle();
				continue;
			}
			if (c == '&')
			{
				printf("\r                                      \r");
				togglekana();
				continue;
			}
			if (c == '-')
			{
				printf("\r                                      \r");
				togglekanji();
				continue;
			}
			if (c == ']')
			{
				printf("\r                                      \r");
				ExtFileDisp();
				continue;
			}
			if (c == '=')
			{
				printf("\r                                      \r");
				altdic(+1);
				continue;
			}
			if (c == '^')
			{
				printf("\r                                      \r");
				altdic(-1);
				continue;
			}
			if (c == '_')
			{
				printf("\r                                      \r");
				seldic();
				continue;
			}
			if (c == '\'')
			{
				printf("\r                                      \r");
				OneShot();
				continue;
			}
			if (c == ';')
			{
				printf("\r                                      \r");
				FiltSet();
				continue;
			}
			if (c == ':')
			{
				printf("\r                                      \r");
				Verbtoggle();
				continue;
			}
			if (c == '[')
			{
				printf("\r                                      \r");
				EMtoggle();
				continue;
			}
			if (c == '$')
			{
				printf("\r                                      \r");
				GDicSet();
				continue;
			}
			if (c == '`')
			{
				printf("\r                                      \r");
				GDicALLtoggle();
				continue;
			}
			if (c == '%')
			{
				printf("\r                                      \r");
				GDictoggle();
				continue;
			}
			if (c == '*')
			{
#ifdef DEMAND_PAGING
				printf("\r                                      \r");
				BuffStats();
#else
				printf("\nNo statistics in this mode!\n");
#endif
				continue;
			}
			/* none of the above, so it must be a Kanji search	*/
			printf("\r                                      \r");
			printf("%sKANJI LOOKUP TYPE:%s ",RVon,RVoff);
			c = getcharxx();

			switch (c)
			{
				case 'c' :	/* a KANJIDIC Index Code	*/
				case 'C' :
					
					printf("\r                                      \r");
					printf("%sINDEX CODE:%s",RVon,RVoff);
					GetKBStr("INDEX CODE:");
					fflush(stdin);
					Dmode =1;
					strcat(fbuff," ");
			/* For bushu or classical radical, ask for stroke count	*/
					if (((fbuff[0] | 0x20) == 'b')||((fbuff[0] | 0x20) == 'c'))
					{
						if (fbuff[1] >= 0xb0)  /* test for "bKANJI"  */
						{
							for (i=0;i<250;i++)
							{
								if((fbuff[1] != radkanj[i][0]) || (fbuff[2] != radkanj[i][1])) continue;
								sprintf(strtmp,"%d",radnos[i]);
								strcpy(fbuff+1,strtmp);
								strcat(fbuff," ");
								printf("Bushu: %s\n",strtmp);
								break;
							}
							if (i == 250)
							{
								printf("Invalid Bushu. Assuming B1 \n");
								strcpy(fbuff,"B1 ");
							}
						}
						printf("\r                                      \r");
						printf("%sSTROKE COUNT (0 selects all):%s",RVon,RVoff);
						cbreakoff();
						fgets(instr,3,stdin);
						i = atoi(instr);
						sprintf(strfilt,"S%d",i);
						cbreakon();
						fflush(stdin);
						fseek(stdin,0L,SEEK_END); /*kill any leftovers*/
						strf = TRUE;
						if (atoi(strfilt+1) == 0) strf = FALSE;
					}
					KLookup();
					instr[0] = 0;
					break;
				case 'm' :	/* "meaning"	*/
				case 'M' :
					printf("\r                                      \r");
					printf("%sMEANING:%s",RVon,RVoff);
					cbreakoff();
					scanf("%s",instr);
					cbreakon();
					fflush(stdin);
					Dmode =1;
					strcpy(fbuff,instr);
					fseek(stdin,0L,SEEK_END); /*kill any leftovers*/
					KLookup();
					instr[0] = 0;
					break;
				case 'j' :	/* JIS code	*/
				case 'J' :
					printf("\r                                      \r");
					printf("%sJIS CODE:%s",RVon,RVoff);
					DoJIS();
					break;
				case 'r' :
				case 'R' :
					DoRADICALS();
					break;
				case 'l' :
				case 'L' :
					DoLOOKUP();
					break;
				case 'k' :
				case 'K' :
					DoKANJI();
					break;
				default :
					ungetc(c,stdin);
					DoKANJI();
					break;
			}
		}
 		if (clipmode)
 		{
 			while(TRUE)
 			{
 				sleep(2);
 				fclip = fopen(Clip_File,"r");
 				if (fclip == NULL)
 				{
 					printf("\nNo Clipboard file! (returning to normal mode.)\n");
 					strcpy(clipstring1,"XXXX");
 					strcpy(clipstring2,"XXXX");
 					clipmode = FALSE;
 					break;
 				}
 				fgets(clipstring1,50,fclip);
 				fclose(fclip);
 				if (clipstring1[strlen(clipstring1)-1] < 32) clipstring1[strlen(clipstring1)-1] = 0;
 				if (strcmp(clipstring1,"quit") == 0)
 				{
 					clipmode = FALSE;
 					printf("\nLeaving Clipboard mode\n");
 					break;
 				}
 				if (strcmp(clipstring1,clipstring2) == 0)
 				{
 					continue;
 				}
 				else
 				{
 					strcpy(clipstring2,clipstring1);
 					strcpy(instr,clipstring1);
 					break;
 				}
			}
		}
		if(strlen(instr) < 2) continue;
		GetEUC(fbuff);
		if (escf) KOut(fbuff);
		sprintf(tempout,"\nSearching for: %s%s%s\n",RVon,fbuff,RVoff);
		KOut(tempout);
		Dmode = 0;
		if (prieng && (fbuff[0] < 128)) /* if priority English key only */
		{
			j = strlen(fbuff);
			fbuff[j+1] = 0;
			for (i=0 ; i < j ; i++) fbuff[i+1] = fbuff[i];
			fbuff[0] = SPTAG;
		}
		Lookup();
	}
}
