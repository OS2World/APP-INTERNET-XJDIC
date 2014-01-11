/**************************************************************************
*                 X J D S E R V C O M M  (V2.0)                   *
*         Japanese-English Dictionary program (X11 version)               *
*                                                                         *
*         These are the common server routines for incorporation          *
*         into the stand-alone  and remote server versions.               *
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
#include <stdlib.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/stat.h>
#ifdef MMAP
#include <sys/mman.h>
#endif
#include "xjdic.h"

#ifndef MAP_FILE
#define MAP_FILE 0
#endif
#ifndef MAP_FAILED
#define MAP_FAILED (void *)-1
#endif

unsigned long dbyte;

unsigned char Dnamet[10][100],XJDXnamet[10][100];
unsigned char *dicbufft[10],dntemp[100];
unsigned long *jdxbufft[10];
unsigned long dichits[10],dicmiss[10];
unsigned long indhits[10],indmiss[10];
unsigned long vbkills=0;
unsigned long diclent[10], indlent[10],indptrt[10];
int i,NoDics,CurrDic;
int xfilelen;

/*====== Prototypes========================================================*/
FILE *xfopen (char *name, char *mode, int *xfilelen);
int xopen (char *name, int *xfilelen);
unsigned long jindex(unsigned long xit);
unsigned char dbchar(unsigned long xit);
void DicSet  ();
int Kstrcmp(int klen,unsigned char *str1);
void DicLoad(int dn);
unsigned char *DicName(int dn);
void DicTest(int dn);
void getvbuff (int *offp, FILE *fp, long vbo);
void SeekErr(int iores);

#ifdef MMAP
FILE *fpd[10],*fpi[10],*fopen();
int fdd[10],fdi[10];
#endif

#ifdef DEMAND_PAGING

/***************************************************************************
* paging routines for Jim's Japanese software
* for use with jdic, jreader, etc
***************************************************************************/

void *vbuffs[NOVB];
void *vbres;
int *vbptr[NOVB];
long usebuff[NOVB], vbusage = 1;
int *doffp[10],*joffp[10];
int MAXDIC,MAXJDX;  /* formerly defines, now set dynamically */
int MAXDICTAB,MAXJDXTAB; 
int novbmax = NOVB,vbread = 0;
FILE *fpd[10],*fpi[10],*fopen();

/* int TRIGGER = FALSE;
int indordic;
int gof,dbck=0; */

/*=====dbchar====returns specified character from dictionary===============*/

unsigned char dbchar(unsigned long it)
{
	int vbo, vbc,ibuff;
	char *myp;
	long it2;
	extern int DicNum;

	it2 = it-1;
/* indordic=0;
dbck++; */
	if ((it2 < 0)||(it2 > diclent[DicNum])) return(10);
	vbo = it2/VBUFFSIZE;   /*page number*/
	vbc = it2 % VBUFFSIZE; /*offset within page  */
/* printf("dbchar - DN: %d vbo: %d vbc: %d\n",DicNum,vbo,vbc); */

	if (doffp[DicNum][vbo] == -1)
	{
		getvbuff(&(doffp[DicNum][vbo]),fpd[DicNum],vbo); /*not resident - get it  */
		dicmiss[DicNum]++;
	}
	else
	{
		dichits[DicNum]++;
	}
	ibuff = doffp[DicNum][vbo];         /*page is (now) resident  */
	usebuff[ibuff] = vbusage++;   /* flag this buffer as most recently used */
	myp = vbuffs[ibuff];
/* printf("dbchar - returns %c\n",myp[vbc]); */
	return(myp[vbc]);
}

/*======jindex  returns specified entry from .jdx file========*/

unsigned long jindex(unsigned long it)
{
	int vbo, vbl,ibuff;
	long *myp;
	long it2;
	extern int DicNum;

/* indordic=1; */
	it2 = it*sizeof(long);
	vbo = it2/VBUFFSIZE;   /*page number*/
	vbl = (it2 % VBUFFSIZE) / sizeof(long); /*offset within page  */
/* printf("jindex - DN: %d it: %ld vbo: %d vbl: %d\n",it,DicNum,vbo,vbl); */

	if (joffp[DicNum][vbo] == -1)
	{
		getvbuff(&(joffp[DicNum][vbo]),fpi[DicNum],vbo); /*not resident - get it  */
		indmiss[DicNum]++;
	}
	else
	{
		indhits[DicNum]++;
	}
	ibuff = joffp[DicNum][vbo];         /*page is (now) resident  */
	usebuff[ibuff] = vbusage++;   /* flag this buffer as most recently used */
	myp = vbuffs[ibuff];
/* printf("jindex - returns %ld\n",myp[vbl]); */
	return(myp[vbl]);
}

/*=====getvbuff===allocates a free virtual buffer and reads in the page===*/

void getvbuff (int *offp, FILE *fp, long vbo)
{
	int ibuff,i,iores;
	long maxu,seekoff;
	extern int DicNum;

/* printf("getvbuff - DN: %d offp: %d vbo: %ld\n",DicNum,offp,vbo); */
/*     find a free buffer, or free the LRU one   */
	vbread++;
	maxu = usebuff[0];
	ibuff = 0;
	for (i = 0; i < NOVB; i++)
	{
		if (usebuff[i] == -1)
		{
			ibuff = i;          /*free buffer available   */
/* printf("getvbuff - buffer %d is free\n",ibuff); */
			break;
		}
		else
		{
			if( usebuff[i] < maxu)   /*look for LRU buffer  */
			{
				maxu = usebuff[i];
				ibuff = i;
			}
		}
	}
	/*  read page into buffer   */
/* printf("getvbuff - buffer %d being loaded\n",ibuff); */
	if(usebuff[ibuff] >= 0) 
	{
		*vbptr[ibuff] = -1;
		vbkills++;
/* TRIGGER = TRUE;
printf("getvbuff - buffer %d being loaded, Dic = %d %d Offset = %d LRUs %d %d %d\n",ibuff,DicNum,indordic,vbo,vbusage,maxu,dbck);
scanf ("%d",&gof); */
	}
	vbptr[ibuff] = offp;
	*vbptr[ibuff] = ibuff;
	seekoff = vbo;
	seekoff *= VBUFFSIZE;
	if((iores = fseek(fp,seekoff,SEEK_SET)) != 0)SeekErr(iores);
	iores = fread(vbuffs[ibuff],1,VBUFFSIZE,fp);
}

#endif

/*====DicSet===Multiple Dictionary and index file Loader=======*/
void DicSet()
{
	int i;

#ifdef DEMAND_PAGING

	vbres = malloc(NOVB * VBUFFSIZE);
	if (vbres == NULL)
	{
		printf("malloc failed for virtual buffers!\n");
		exit(1);
	}
	for (i = 0; i < NOVB; i++)
	{
		vbuffs[i] = vbres;
		usebuff[i] = -1;
		vbres+=VBUFFSIZE;
	}
#endif

	for (i = 0; i<=NoDics; i++) DicTest(i);
	for (i = 0; i<=NoDics; i++) DicLoad(i);
}

/*====DicTest check Dictionary and index files=======*/
void DicTest(int dn)
{
	long testwd[1];
	int diclenx;

	extern int jiver;
	FILE *fpd,*fopen();

	dichits[dn] = 0;
	dicmiss[dn] = 0;
	indhits[dn] = 0;
	indmiss[dn] = 0;

	fpd = xfopen(Dnamet[dn],"rb", &diclenx);
  	diclenx++;
  	fclose(fpd);
  	fpd = xfopen(XJDXnamet[dn],"rb", &xfilelen);
	fread(&testwd[0],sizeof(long),1,fpd);
	if (testwd[0] != (diclenx+jiver))
	{
		printf ("The %s dictionary and index files do not match! \n",Dnamet[dn]);
		exit(1);
	}
	fclose(fpd);
}

#ifdef RAM_LOAD
/*====DicLoad check & load Dictionary and index files=======*/
/*   (Old version; load everything in RAM)      */

void DicLoad(int dn)
{
  	int nodread;
	/* struct stat *buf;  no longer used here  */

	extern int jiver;
	FILE *fpd,*fopen();

	printf("Loading Dictionary: %d [%s]\n",dn,DicName(dn));
  	fpd = xfopen(Dnamet[dn],"rb", &xfilelen);
	diclent[dn] = xfilelen;

  	diclent[dn]++;
	dicbufft[dn] = (unsigned char *)malloc(((diclent[dn]+100) * sizeof(unsigned char)));
	if(dicbufft[dn] == NULL)
	{
		fprintf(stderr,"malloc() for dictionary failed.\n");
		fclose(fpd);
	exit(1);
	}
	nodread = diclent[dn]/1024;
	dbyte = fread((unsigned char *)dicbufft[dn]+1, 1024, nodread, fpd);
	nodread = diclent[dn] % 1024;
	dbyte = fread((unsigned char *)(dicbufft[dn]+(diclent[dn]/1024)*1024)+1, nodread,1, fpd);
	fclose(fpd);
	dicbufft[dn][0] = 0xa;
  	dbyte = diclent[dn];
  	fpd = xfopen(XJDXnamet[dn],"rb", &xfilelen);
        indlent[dn] = xfilelen;
        jdxbufft[dn] = (unsigned long *)malloc((indlent[dn]+1024) * sizeof(unsigned char));
        if(jdxbufft[dn] == NULL)
        {
                fprintf(stderr,"malloc() for index failed.\n");
                fclose(fpd);
        exit(1);
        }
	indptrt[dn] = indlent[dn]/sizeof(long)-1;
        nodread = indlent[dn]/1024+1;
	fread((long *)jdxbufft[dn],1024,nodread,fpd);
	if (jdxbufft[dn][0] != (diclent[dn]+jiver))
	{
		printf ("The dictionary and index files do not match! \n");
		exit(1);
	}
	fclose(fpd);
}

#endif

#ifdef DEMAND_PAGING
/*====DicLoad check & load Dictionary and index files=======*/
/*   (Paging version)      */
void DicLoad(int dn)
{
  	int i,len;

#ifndef QUIET
	printf("Initializing Dictionary: %d [%s]\n",dn,DicName(dn));
#endif
  	fpd[dn] =xfopen(Dnamet[dn],"rb", &xfilelen);
	diclent[dn] = xfilelen;

  	diclent[dn]++;
	len = (diclent[dn]/VBUFFSIZE)+1;
	doffp[dn] = (int *)malloc(len * sizeof(int));
	if(doffp[dn] == NULL)
	{
		fprintf(stderr,"malloc() for dictionary page-table failed.\n");
		exit(1);
	}
	for (i = 0; i < len; i++) doffp[dn][i] = -1;

  	fpi[dn] = xfopen(XJDXnamet[dn],"rb", &xfilelen);
        indlent[dn] = xfilelen;
	indptrt[dn] = indlent[dn]/sizeof(long)-1;
	len = (indlent[dn]/VBUFFSIZE)+1;
        joffp[dn] = (int *)malloc(len * sizeof(int));
        if(joffp[dn] == NULL)
        {
                fprintf(stderr,"malloc() for index page-table failed.\n");
        	exit(1);
        }
	for (i = 0; i < len; i++) joffp[dn][i] = -1;
}
#endif

#ifdef MMAP
/*====DicLoad check & load Dictionary and index files=======*/
/*   (Memory-mapped I/O version)      */
void DicLoad(int dn)
{
  	int i,len;

#ifndef QUIET
	printf("Initializing Dictionary: %d [%s]\n",dn,DicName(dn));
#endif
  	fdd[dn] =xopen(Dnamet[dn],&xfilelen);
	diclent[dn] = xfilelen;
	if ((dicbufft[dn] = mmap(0, xfilelen, PROT_READ, MAP_FILE | MAP_SHARED, fdd[dn],0)) == MAP_FAILED)
	{
		printf ("Unable to map %s! [%s]\n",DicName(dn),strerror(errno));
		exit(1);
	}
  	diclent[dn]++;
  	fdi[dn] = xopen(XJDXnamet[dn],&xfilelen);
        indlent[dn] = xfilelen;
	indptrt[dn] = indlent[dn]/sizeof(long)-1;
	if ((jdxbufft[dn] = (long *) mmap(0, xfilelen, PROT_READ, MAP_FILE | MAP_SHARED, fdi[dn],0)) == MAP_FAILED)
	{
		printf ("Unable to map %s.xjdx! [%s]\n",DicName(dn),strerror(errno));
		exit(1);
	}
}
#endif
#ifdef RAM_LOAD
/*=====dbchar====returns specified character from a dictionary===============*/
/* 	This routine looks funny, because it is the remnant of much more
	complex code in JDIC/JREADER which did demand-paging at this point   */

unsigned char dbchar(unsigned long xit)
{
	extern int DicNum;

	return(dicbufft[DicNum][xit]);
}
#endif

#ifdef MMAP
/*=====dbchar====returns specified character from a dictionary===============*/
/* 	This routine looks funny, because it is the remnant of much more
	complex code in JDIC/JREADER which did demand-paging at this point   */

unsigned char dbchar(unsigned long xit)
{
	extern int DicNum;
	long it2;

	it2 = xit-1;
	if ((it2 < 0)||(it2 > diclent[DicNum])) return(10);

	return(dicbufft[DicNum][it2]);
}
#endif
#if defined (RAM_LOAD) || defined (MMAP)
/*======jindex  returns specified entry from .xjdx file========*/

unsigned long jindex(unsigned long xit)
{
	extern int DicNum;

	return(jdxbufft[DicNum][xit]);
}

#endif

/*=========string comparison function used in binary search ==========*/
/*	This one is used by the main dictionary search		*/

int Kstrcmp(int klen,unsigned char *str1)
{
	unsigned c1,c2;
	int i,rc1,rc2;
	extern long it;

/* effectively does a strnicmp on two "strings" 
   except it will make katakana and hiragana match (EUC A4 & A5) */

/* if (TRIGGER) printf("KSTRCMP called: %d %c%c\n",klen,str1[0],str1[1]); */
	for (i = 0; i<klen ; i++)
	{
		c1 = str1[i];
		c2 = dbchar(jindex(it)+i);
		if ((c1 == '\0')||(c2 == '\0')) return(0);
		if ((i % 2) ==0)
		{
			if (c1 == 0xA5)
			{
				c1 = 0xA4;
			}
			if (c2 == 0xA5)
			{
				c2 = 0xA4;
			}
		}
		if ((c1 >= 'A') && (c1 <= 'Z')) c1 |= 0x20; /*fix ucase*/
		if ((c2 >= 'A') && (c2 <= 'Z')) c2 |= 0x20;
		if (c1 != c2 ) 
		{
			rc1 = c1;
			rc2 = c2;
			return(rc1-rc2);
		}
	}
	return(0);
}
