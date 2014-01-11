/**************************************************************************
*                 X  J  D  C  O  M  M                                     *
*              some common routines                                       *
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
#include <unistd.h>
#include <stdlib.h>
#include <signal.h>
#include <errno.h>
#ifdef MMAP
#include <fcntl.h>
#endif
#include "xjdic.h"

#define FALSE 0
#define TRUE 1

#ifdef XJDCLSERV
extern int portno;
extern unsigned char host[];
#endif

extern unsigned char Dnamet[10][100];

int stringcomp(unsigned char *s1, unsigned char *s2);
struct stat buf;

#ifdef MMAP
/*+++++++++ xopen +++ does a open, but tries the dicdir first +++*/
/*
	xopen generalizes the dictionary and other file opening, by:

		trying the "dicdir", and then current directories
		returning the file length as well as the pointer to FILE
	Note that it is read-only.
								*/
int xopen(char *file_name, int *xfilelen)
{
	int fx;

	extern char DicDir[];
	char *fnbuff;

	fnbuff = (char *)malloc(strlen(DicDir) + strlen(file_name)+10);
	if (fnbuff == NULL)
	{
		printf("malloc failure opening: %s\n",file_name);
		exit(1);
	}
	strcpy(fnbuff,DicDir);
	if (fnbuff[strlen(fnbuff)-1] != '/') strcat (fnbuff,"/");
	strcat(fnbuff,file_name);
	fx = open(fnbuff,O_RDONLY);
	if (fx >= 0)
	{
		if(stat(fnbuff, &buf) != 0)
		{
			printf ("Stat() error (l)for %s [%s]\n",fnbuff,strerror(errno));
			exit(1);
		}
		*xfilelen = (buf.st_size);
		free(fnbuff);
		return(fx);
	}
	fx = open(file_name,O_RDONLY);
	if (fx >= 0) 
	{
		if(stat(file_name, &buf) != 0)
		{
			printf ("Stat() error (s) for %s [%s]\n",file_name,strerror(errno));
			exit(1);
		}
		*xfilelen = buf.st_size;
		return(fx);
	}
	printf("Unable to open: %s\n",file_name);
	exit(1);
}
#endif

/*+++++++++ xfopen +++ does a fopen, but tries the dicdir first +++*/
/*
	xfopen generalizes the dictionary and other file opening, by:

		trying the "dicdir", and then current directories
		returning the file length as well as the pointer to FILE
								*/
FILE  *xfopen(char *file_name, char *file_mode, int *xfilelen)
{
	FILE *fx, *fopen();

	extern char DicDir[];
	char *fnbuff;

/* printf ("XFOPEN: fn=%s mode=%s stream_p=%p\n",file_name,file_mode,fx); */
	fnbuff = (char *)malloc(strlen(DicDir) + strlen(file_name)+10);
	if (fnbuff == NULL)
	{
		printf("malloc failure opening: %s\n",file_name);
		exit(1);
	}
	strcpy(fnbuff,DicDir);
	if (fnbuff[strlen(fnbuff)-1] != '/') strcat (fnbuff,"/");
	strcat(fnbuff,file_name);
	fx = fopen(fnbuff,file_mode);
	if (fx != NULL)
	{
		if(stat(fnbuff, &buf) != 0)
		{
			printf ("Stat() error (l)for %s [%s]\n",fnbuff,strerror(errno));
			exit(1);
		}
		*xfilelen = (buf.st_size);
		free(fnbuff);
/* printf ("XFOPEN: stream_p=%p addr = %p\n",fx,&fx); */
		return(fx);
	}
	fx = fopen(file_name,file_mode);
	if (fx != NULL) 
	{
		if(stat(file_name, &buf) != 0)
		{
			printf ("Stat() error (s) for %s [%s]\n",file_name,strerror(errno));
			exit(1);
		}
		*xfilelen = buf.st_size;
/* printf ("XFOPEN: stream_p=%p addr = %p\n",fx,&fx); */
		return(fx);
	}
	printf("Unable to open: %s\n",file_name);
	exit(1);
}
/*=========DicName====returns name of dictionary================*/
unsigned char *DicName(int dn)
{
	register unsigned char *dp,*dp2;

	dp  = Dnamet[dn];
	if((dp2 = strrchr(dp,'/')) == NULL) return(dp);
	return (dp2+1);
}
/*=====xjdicrc - access and analyze "xjdicrc" file (if any)==============*/
void xjdicrc()
{
	unsigned char xjdicdir[128],rcstr[80],*rcwd;
	int ft,fn;
	extern int thisdic;
	extern char DicDir[];
	FILE *fm,*fopen();

#ifdef XJDDIC
	extern unsigned char Dnamet[10][100],XJDXnamet[10][100];
	extern unsigned char *dicbufft[10];
	extern unsigned long diclent[10], indkent[10],indptrt[10];
	extern int NoDics;
#endif
	extern unsigned char ENVname[], KDNSlist[];
	extern unsigned char EXTJDXname[], EXTname[], Rname[], Vname[], ROMname[];
	extern unsigned char RKname[];
	extern unsigned char filtnames[NOFILT][50],filtcodes[NOFILT][10][10];
	extern int Omode, Jverb, nofilts, filtact[], filtcoden[], filttype[], filton[];
	extern int RVACTIVE;
	extern unsigned char cl_rcfile[];
#ifdef XJDFRONTEND
	extern unsigned char GPL_File[];
	extern unsigned char Clip_File[];
	extern int KImode;
#endif

	strcpy(DicDir,ENVname); /* added by nakahara@debian.org */
	while(TRUE)
	{
		if (strlen(cl_rcfile) > 0)
		{
			fm = fopen(cl_rcfile,"r");
			if (fm != NULL) break;
			else
			{
				printf("Control file: %s cannot be accessed!\n",cl_rcfile);
			}
		}
		xjdicdir[0] = '\0';
		if (strlen(ENVname) > 2)
		{
			strcpy(xjdicdir,ENVname);
			strcat(xjdicdir,"/");
		}
		else    
		{
			strcpy(xjdicdir,getenv("HOME"));
			strcat(xjdicdir,"/");
		}
		strcat(xjdicdir,".xjdicrc");
		fm = fopen(xjdicdir,"r");
		if (fm != NULL) break;
		strcpy(xjdicdir,".xjdicrc");
		fm = fopen(xjdicdir,"r");
		if (fm != NULL) break;
		if (getenv("HOME") != NULL)
		{
			strcpy(xjdicdir,getenv("HOME"));
			strcat(xjdicdir,"/");
			strcat(xjdicdir,".xjdicrc");
			fm = fopen(xjdicdir,"r");
			if (fm != NULL) break;
		}
		printf("No control file detected!\n");
		return;
	}
	if (fm != NULL)
	{
		while(fgets(rcstr,79,fm) != NULL)
		{
			rcwd = (unsigned char *)strtok(rcstr," \t");
/*  dicdir works for all modes   */
			if( stringcomp((unsigned char *)"dicdir",rcwd) == 0)
			{
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				strcpy(DicDir,rcwd);
				continue;
			}
#ifdef XJDCLSERV
			if( stringcomp((unsigned char *)"port",rcwd) == 0)
			{
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				portno = atoi(rcwd);
				continue;
			}
			if( stringcomp((unsigned char *)"server",rcwd) == 0)
			{
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				strcpy(host,rcwd);
				continue;
			}
#endif
#ifdef XJDFRONTEND
			if( stringcomp((unsigned char *)"omode",rcwd) == 0)
			{
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				rcwd[0] = rcwd[0] | 0x20;
				if(rcwd[0] == 'j') Omode = 0;
				if(rcwd[0] == 'e') Omode = 1;
				if(rcwd[0] == 's') Omode = 2;
				continue;
			}
			if( stringcomp((unsigned char *)"kanamode",rcwd) == 0)
			{
				KImode = 0;
				continue;
			}
			if( stringcomp((unsigned char *)"exactmatch",rcwd) == 0)
			{
				EMtoggle ();
				continue;
			}
#endif
#ifdef XJDDIC
			if( stringcomp((unsigned char *)"dicfile",rcwd) == 0)
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
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				strcpy(Dnamet[thisdic],rcwd);
				strcpy(XJDXnamet[thisdic],rcwd);
				strcat(XJDXnamet[thisdic],".xjdx");
				continue;
			}
#endif
#ifdef XJDFRONTEND
                        if( stringcomp((unsigned char *)"gnufile",rcwd) == 0)
                        {
                                rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
                                strcpy(GPL_File,rcwd);
                                continue;
                        }
#endif
#ifdef XJDFRONTEND
                        if( stringcomp((unsigned char *)"clipfile",rcwd) == 0)
                        {
                                rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
                                strcpy(Clip_File,rcwd);
                                continue;
                        }
#endif
#ifdef XJDFRONTEND
                        if( stringcomp((unsigned char *)"extfile",rcwd) == 0)
                        {
                                rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
                                strcpy(EXTname,rcwd);
                                strcpy(EXTJDXname,rcwd);
                                strcat(EXTJDXname, ".xjdx");
                                continue;
                        }
#endif
#ifdef XJDFRONTEND
			if( stringcomp((unsigned char *)"rvdisplay",rcwd) == 0)
			{
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				if( stringcomp((unsigned char *)"on",rcwd) == 0) RVACTIVE = TRUE;
				if( stringcomp((unsigned char *)"off",rcwd) == 0) RVACTIVE = FALSE;
				continue;
			}
#endif
#ifdef XJDFRONTEND
			if( stringcomp((unsigned char *)"kdnoshow",rcwd) == 0)
			{
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				strcpy(KDNSlist,rcwd);
				continue;
			}
#endif
#ifdef XJDDIC
			if( stringcomp((unsigned char *)"kdicfile",rcwd) == 0)
			{
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				strcpy(Dnamet[0],rcwd);
				strcpy(XJDXnamet[0],rcwd);
				strcat(XJDXnamet[0],".xjdx");
				continue;
			}
#endif
#ifdef XJDFRONTEND
			if( stringcomp((unsigned char *)"radkfile",rcwd) == 0)
			{
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				strcpy(RKname,rcwd);
				continue;
			}
			if( stringcomp((unsigned char *)"radfile",rcwd) == 0)
			{
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				strcpy(Rname,rcwd);
				continue;
			}
			if( stringcomp((unsigned char *)"verbfile",rcwd) == 0)
			{
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				strcpy(Vname,rcwd);
				continue;
			}
			if( stringcomp((unsigned char *)"romfile",rcwd) == 0)
			{
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				strcpy(ROMname,rcwd);
				continue;
			}
			if( stringcomp((unsigned char *)"jverb",rcwd) == 0)
			{
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				if(stringcomp(rcwd,(unsigned char *)"on") == 0) Jverb = TRUE;
				if(stringcomp(rcwd,(unsigned char *)"off") == 0) Jverb = FALSE;
				continue;
			}
			if( stringcomp((unsigned char *)"filt",rcwd) == 0)
			{
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				sscanf(rcwd,"%d",&fn);
				if ((fn < 0)||(fn > NOFILT)) continue;
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				sscanf(rcwd,"%d",&ft);
				if (ft > 2) continue;
				filttype[fn] = ft;
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				filton[fn] = FALSE;
				if(stringcomp((unsigned char *)"on",rcwd) == 0) 
				{
					filton[fn] = TRUE;
					nofilts  = TRUE;
				}
				rcwd = (unsigned char *)strtok(NULL,"\"");
				strcpy(filtnames[fn],rcwd);
				ft=0;
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				while(rcwd != NULL)
				{
					strcpy(filtcodes[fn][ft],rcwd);
					ft++;
					rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				}
				if(ft==0)continue;
				filtcoden[fn] = ft;
				filtact[fn] = TRUE;
				continue;
			}
#endif
		}
	}
	else
	{
		printf("No .xjdicrc file detected\n");
		return;
	}
	fclose(fm);
}

/*====stringcomp==stricmp & strcasecmp pulled together=========*/
/*    (my own routine, because different systems need one or the other    */
int stringcomp(unsigned char *s1, unsigned char *s2)
{	
	int i;	 unsigned char c1,c2;
	
	for(i = 0; i < strlen(s1);i++)
	{
		c1 = s1[i];
		if (c1 < 0x60) c1 = (c1|0x20);
		c2 = s2[i];
		if (c2 < 0x60) c2 = (c2|0x20);
		if (c1 != c2) return(1);
	}
	return (0);
}
/*====SeekErr==Common error routine for seeking==================*/
void SeekErr(int iores)
{
	printf("\nSeek error %d\n",iores);
	exit(1);
}
