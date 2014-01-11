/**************************************************************************
*                          X J D R A D                                    *
*          Displays Radical Table for Lookup Usage                        *
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
#include <unistd.h>

#include "xjdic.h"

#define RADPERLINE 20

struct stat *xbuf;

unsigned char RKname[50] = {"radkfile"};
unsigned char IRKname[50] = {"radkfile"};
unsigned char DicDir[100];
unsigned char sver[] = {SVER};
unsigned char ENVname[50];
unsigned char testline[200];
unsigned char RVon[] = {0x1b,'[','7','m',0};
unsigned char RVoff[] = {0x1b,'[','m',0};

FILE  *xfopen(char *file_name, char *file_mode, int *xfilelen);
void xjdicrc();
void RadDisp();

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
/*=====RadDisp===Display Radical Data==============================*/
void RadDisp()
{
	int i,j,k,l,flen;
	FILE *fk,*fopen();
	unsigned char *ptr;

	fk = xfopen(RKname,"r",&flen);
	k=99;
	j = 0;
	printf("RADICAL TABLE FOR USE WITH XJDIC RADICAL LOOKUP FUNCTION\n\n");
	while(!feof(fk))
	{
		fgets(testline,199,fk);
		if(feof(fk)) break;
		testline[strlen(testline)-1] = 0;
		if (testline[0] != '$') continue;
		ptr = strtok(testline+4," ");
		l = atoi(ptr);
		if (l != k)
		{
			k = l;
			printf(" %s%s%s ",RVon,ptr,RVoff);
			if (k < 10) printf(" ");
			if(++j % RADPERLINE == 0) printf("\n");
		}
		printf(" %c%c ",testline[2],testline[3]);
		if(++j % RADPERLINE == 0) printf("\n");
	}
	fclose(fk);
	printf("\n");
}
/*+++++++++ xfopen +++ does a fopen, but tries the dicdir first +++*/
/*
	xfopen generalizes the dictionary and other file opening, by:

		trying the "dicdir", and then current directories
		returning the file length as well as the pointer to FILE
								*/
FILE  *xfopen(char *file_name, char *file_mode, int *xfilelen)
{
	FILE *fx, *fopen();

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
		if(stat(fnbuff, xbuf) != 0)
		{
			printf ("Stat() error (l)for %s [%s]\n",fnbuff,strerror(errno));
			exit(1);
		}
		*xfilelen = (xbuf->st_size);
		free(fnbuff);
/* printf ("XFOPEN: stream_p=%p addr = %p\n",fx,&fx); */
		return(fx);
	}
	fx = fopen(file_name,file_mode);
	if (fx != NULL) 
	{
		if(stat(file_name, xbuf) != 0)
		{
			printf ("Stat() error (s) for %s [%s]\n",file_name,strerror(errno));
			exit(1);
		}
		*xfilelen = xbuf->st_size;
/* printf ("XFOPEN: stream_p=%p addr = %p\n",fx,&fx); */
		return(fx);
	}
	printf("Unable to open: %s\n",file_name);
	exit(1);
}
/*=====xjdicrc - access and analyze "xjdicrc" file (if any)==============*/
void xjdicrc()
{
	unsigned char xjdicdir[128],rcstr[80],*rcwd;
	int ft,fn;
	FILE *fm,*fopen();

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
	if (fm == NULL)
	{
		strcpy(xjdicdir,".xjdicrc");
		fm = fopen(xjdicdir,"r");
	}
	if (fm == NULL)
	{
		strcpy(xjdicdir,getenv("HOME"));
		strcat(xjdicdir,"/");
		strcat(xjdicdir,".xjdicrc");
		fm = fopen(xjdicdir,"r");
	}
	if (fm != NULL)
	{
		while(fgets(rcstr,79,fm) != NULL)
		{
			rcwd = (unsigned char *)strtok(rcstr," \t");
			if( stringcomp((unsigned char *)"dicdir",rcwd) == 0)
			{
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				strcpy(DicDir,rcwd);
				continue;
			}
			if( stringcomp((unsigned char *)"radkfile",rcwd) == 0)
			{
				rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
				strcpy(RKname,rcwd);
				continue;
			}
		}
	}
	else
	{
		printf("No .xjdicrc file detected\n");
		return;
	}
	fclose(fm);
}

/*                  M A I N                                      */

main()
{
	int i,j;
  	unsigned char *dicenv,strtmp[50];
	
  	printf("XJDRAD version %s (Japanese Dictionary) Copyright J.W.Breen 2003.\n",sver);

	xbuf = (void *)malloc(sizeof(struct stat));
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
        sprintf(RKname, "%s/%s", dicenv, IRKname);
	xjdicrc();
	RadDisp();
}
