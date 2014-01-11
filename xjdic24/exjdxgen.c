/**************************************************************************
*                   E X J D X G E N
*                                                   Author: Jim Breen
*
*   This is the Unix version of EJDXGEN, ported from MS-DOS
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

#include <sys/types.h>
#include <sys/stat.h>

#include <stdio.h>
/*#include <stdlib.h>*/
#include <ctype.h>
#include <string.h>
#include "xjdic.h"

#define TRUE 1
#define FALSE 0
#define EXLIM 100

unsigned char *db;
unsigned char ENVname[50];
unsigned char *dicenv;
struct stat *buf;
unsigned long dbyte;
unsigned long  *jindex;
unsigned long indptr,llone,charno,recpos,charnost;
int State;
unsigned char Dname[80] = {"edictext"};
unsigned char JDXname[80] = {"edictext.xjdx"};
int jiver = 14;		/*The last time the index structure changed was Version1.4*/

/*====== prototypes=================================================*/
int stringcomp(unsigned char *s1, unsigned char *s2);
void jqsort(long i, long j);
int Kstrcmp(unsigned long lhs, unsigned long rhs);
/*====== end prototypes=================================================*/

int stringcomp(unsigned char *s1, unsigned char *s2)
{
	int i;
	unsigned char c1,c2;

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

/*====function to Load Dictionary and load/create index table=======*/
main(argc,argv)
int argc;
unsigned char **argv;
{
  FILE *fp,*fopen();
  unsigned long schi,diclen,indlen;
  int i,inwd,saving,nodread;
  unsigned char c;
  unsigned char **ap;

  printf("\nEXJDXGEN V2.0 Extension Index Table Generator for XJDIC. \n      Copyright J.W. Breen, 1995\n");
  if (argc > 1)
  {
	ap = argv;
	ap++;
	if(strcmp(*ap,"-h") == 0)
	{
		printf("\nThere are two command-line options:\n");
		printf("  -h  this display\n");
		printf("  filename - file to be indexed\n\n");
		exit(0);
	}
	strcpy(Dname,*ap);
	strcpy(JDXname,*ap);
	strcat(JDXname,".xjdx");
    printf("Commandline request to use files %s and %s \n",Dname,JDXname);
  }
  inwd = FALSE;
  indptr = 1;
  llone = 1;
  buf = (void *)malloc(1000);
  if(stat(Dname, buf) != 0)
  {
	 perror(NULL);
	 printf("Cannot stat: %s \n",Dname);
	 exit(1);
  }
  diclen = buf->st_size;
  printf("\nWARNING!!  This program may take a long time to run .....\n");

  puts ("\nLoading Dictionary file.  Please wait.....\n");
  fp=fopen(Dname,"rb");
  if (fp==NULL )
  {
	printf("\nCannot open dictionary file\n");
	exit(1);
  }
  db = (unsigned char *)malloc((diclen+100) * sizeof(unsigned char));
  if(db == NULL)
  {
      fprintf(stderr,"malloc() for dictionary failed.\n");
      fclose(fp);
      exit(1);
  }
  nodread = diclen/1024;
  dbyte = fread((unsigned char *)db+1, 1024, nodread, fp);
  nodread = diclen % 1024;
  dbyte = fread((unsigned char *)(db+(diclen/1024)*1024)+1, nodread,1, fp);
  fclose(fp);
  diclen++;
  dbyte = diclen;
  db[diclen] = 10;
  db[0] = 10;
  printf("Dictionary size: %ld bytes.\n",dbyte);
  indlen = diclen / 2;
  jindex = (unsigned long *)malloc(indlen);
  if(jindex == NULL)
  {
	  fprintf(stderr,"malloc() for index table failed.\n");
	  fclose(fp);
	  exit(1);
  }
  printf("Parsing.... \n");
  indptr = 1;
  saving = FALSE;
  charno = -1;
  State = 0;
  for (schi =0; schi < dbyte; schi++) /* scan whole dictionary  */
  {
	  c = db[schi];
	  charno++;
	  if (c == 0x0a)
	  {
		recpos = charno+1;
		continue;
	  }
	  switch (State)
	  {
	  case 0 :	/* Looking for < 	*/
		if (c == '<') State = 1;
		break;
	  case 1 :	/* Inside <..>, but nothing started yet	*/
		if (c >= 127)
		{
			saving = TRUE;
			charnost = charno-1;
			State = 2;
			break;
		}
		else
		{
			State = 3;
	  		schi--;
	  		charno--;
			break;
		}
	case 2 :	/* storing keywords  */
		if (c >= 127)
		{
			break;
		}
		else
		{
			jindex[indptr] = charnost;
			jindex[indptr+1] = recpos;
			indptr+=2;
			if (indptr > indlen/sizeof(long))
			{
			  	printf("Index table overflow. Dictionary too large?\n");
			  	exit(1);
			}
			saving = FALSE;
	  		schi--;
	  		charno--;
			State = 3;
			break;
		}
	case 3 : 	/* encountered non-JIS	*/
		if (c == '>')
		{
			State = 0;
			break;
		}
		if (c == '[')
		{
			State = 4;
			break;
		}
		if (c >= 127)
		{
			schi--;
  			charno--;
			State = 1;
		}
		break;
	case 4 :	/* skip all until ]		*/
		if (c == ']') State = 1;
		break;
	}
    }
    indptr-=2;
    printf("Index entries: %ld  \nSorting (this is slow)......\n",indptr);
    jqsort(llone,(indptr/2)+1);
    printf("Sorted\nWriting index file ....\n");
    fp = fopen(JDXname,"wb");
    if (fp==NULL )
    {
    	printf("\nCannot open %s output file\n",JDXname);
    	exit(1);
    }
  jindex[0] = diclen+jiver;
  fwrite(jindex,sizeof(long),indptr+2,fp);
  fclose(fp);
}
/*======function to sort jindex table====================*/

void jqsort(long lhsr, long rhsr)
{
	long i,last,midp,lhs,rhs;
	unsigned long temp,temp2;

	lhs = ((lhsr-1)*2)+1;
	rhs = ((rhsr-1)*2)+1;
	if (lhs >= rhs) return;
	/* Swap ( lhs , (lhs+rhs)/2);*/
	midp = (lhs+rhs)/2;
	if (!(midp & 1)) midp--;
	temp = jindex[lhs];
	temp2 = jindex[lhs+1];
	jindex[lhs] = jindex[midp];
	jindex[lhs+1] = jindex[midp+1];
	jindex[midp] = temp;
	jindex[midp+1] = temp2;
	last = lhs;
	for (i = lhs+2;i <= rhs; i+=2)
		{
			if (Kstrcmp(jindex[i],jindex[lhs]) < 0)
			{
				/* Swap(++last,i);*/
				last+=2;
				temp = jindex[i];
				jindex[i] = jindex[last];
				jindex[last] = temp;
				temp = jindex[i+1];
				jindex[i+1] = jindex[last+1];
				jindex[last+1] = temp;
			}
		}
/*	Swap (lhs,last);*/
	temp = jindex[lhs];
	jindex[lhs] = jindex[last];
	jindex[last] = temp;
	temp = jindex[lhs+1];
	jindex[lhs+1] = jindex[last+1];
	jindex[last+1] = temp;
	jqsort((lhs/2)+1,last/2);
	jqsort((last/2)+2,(rhs/2)+1);
}
/*=====string comparison used by jqsort==========================*/
int Kstrcmp(unsigned long lhs, unsigned long rhs)
{
	int i,c1,c2;
/* effectively does a strnicmp on two "strings" within the dictionary,
   except it will make katakana and hirgana match (EUC A4 & A5) */

	for (i = 0; i<20 ; i++)
	{
		c1 = db[lhs+i+1];
		c2 = db[rhs+i+1];
		if ((i % 2) == 0)
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
		if ((c1 >= 'A') && (c1 <= 'Z')) c1 |= 0x20;
		if ((c2 >= 'A') && (c2 <= 'Z')) c2 |= 0x20;
		if (c1 != c2 ) break;
	}
	return(c1-c2);
}

