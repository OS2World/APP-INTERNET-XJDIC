/**************************************************************************
*                     X J D X G E N
*                                                   Author: Jim Breen
*           Index (.xjdx) generator program fron XJDIC            
*
*		V2.3 - indexes JIS X 0212 (3-byte EUC) kanji
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
#define SPTAG '@'
#define EXLIM 100
#define TOKENLIM 40

unsigned char *db;
unsigned char ENVname[50];
unsigned char *dicenv;
struct stat *buf;
unsigned long dbyte;
unsigned long  *jindex;
unsigned long indptr,llone;
unsigned char ctl_file[80] = {".xjdicrc"};
unsigned char Dname[80] = {"edict"};
unsigned char JDXname[80] = {"edict.xjdx"};
unsigned char EDname[80] = {"edict"};
unsigned char EJDXname[80] = {"edict.xjdx"};
unsigned char exlist[EXLIM][11];	/* list of words to be excluded */
int excount,exlens[EXLIM];
int jiver = 14;		/*The last time the index structure changed was Version1.4*/

/*====== prototypes=================================================*/
int stringcomp(unsigned char *s1, unsigned char *s2);
void jqsort(long i, long j);
int Kstrcmp(unsigned long lhs, unsigned long rhs);
void xjdicrc();
int alphaoreuc(unsigned char x);

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
  unsigned long possav,schi,diclen,indlen;
  int i,inwd,cstrp,saving,isc,nodread;
  int arg_c;
  unsigned char c;
  unsigned char currstr[TOKENLIM],strtmp[50];
  unsigned char **ap;

  printf("\nXJDXGEN V2.4 Index Table Generator for XJDIC. \n      Copyright J.W. Breen, 2003\n");
  ap = argv;
  arg_c = argc;
  while (arg_c > 1)
  {
	ap++;
	if(strcmp(*ap,"-h") == 0)
	{
		printf("\nThe command-line options are:\n");
		printf("  -h  this display\n");
		printf("  -c  control file\n");
		printf("  filename - file to be indexed\n\n");
		exit(0);
	}
	if(strcmp(*ap,"-c") == 0)
	{
		ap++;
		strcpy(ctl_file,*ap);
    		printf("Commandline request to use control file %s\n",ctl_file);
		arg_c-=2;
		continue;
	}
	strcpy(strtmp,*ap);
	strcpy(Dname,*ap);
	strcpy(JDXname,*ap);
	strcat(JDXname,".xjdx");
    	printf("Commandline request to use files %s and %s \n",Dname,JDXname);
	ap++;
	arg_c--;
  }
  xjdicrc();
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
  indlen = (diclen * sizeof(long))/4;
  jindex = (unsigned long *)malloc(indlen);
  if(jindex == NULL)
  {
	  fprintf(stderr,"malloc() for index table failed.\n");
	  fclose(fp);
	  exit(1);
  }
  printf("Parsing.... \n");
  /*this is the dictionary parser. It places an entry in jindex for every
   kana/kanji string and every alphabetic string it finds which is >=3
   characters and is not on the "exclude" list */
  indptr = 1;
  saving = FALSE;
  cstrp = 0;
  for (schi =0; schi < dbyte; schi++) /* scan whole dictionary  */
  {
	  c = db[schi];
	  if (inwd)
	  {
		  if ((alphaoreuc(c))||(c == '-')||(c == '.')||((c >= '0') && (c <= '9')))
		  {
			  currstr[cstrp] = c;
			  if(cstrp < TOKENLIM-1) cstrp++;
		  }
		  else
		  {
			  currstr[cstrp] = '\0';
			  inwd = FALSE;
			  if ((strlen(currstr) <= 2) && (currstr[0] < 127))saving = FALSE;
			  if ((strlen(currstr) == 2) && (currstr[1] <= '9'))saving = TRUE;
			  if (saving && (currstr[0] > 127))
			  {
				  possav = jindex[indptr];
				  indptr++;
					if (indptr > indlen/sizeof(long))
					{
					printf("Index table overflow. Dictionary too large?\n");
					exit(1);
					}
/* generate index for *every* kanji in key */
				i = 2;
				if (currstr[0] == 0x8f) i++;
				for ( ; i < strlen(currstr); i+=2)
				{
					if((currstr[i] >= 0xb0) || (currstr[i] == 0x8f))
					{
						jindex[indptr] = possav+i;
						indptr++;
                                  		if (indptr > indlen/sizeof(long))
                                  		{
                                          		printf("Index table overflow. Dictionary too large?\n");
                                          		exit(1);
                                  		}
					}
					if (currstr[i] == 0x8f) i++;
				}
			  }
			  if (saving && (currstr[0] < 127))
			  {
				  indptr++;
				  if (indptr > indlen/sizeof(long))
				  {
					  printf("Index table overflow. Dictionary too large?\n");
					  exit(1);
				  }
/* If this is non-Japanese, and has a 'SPTAGn' tag, generate two indices */
				  if ( currstr[0] == SPTAG)
				  {
				  	jindex[indptr] = jindex[indptr-1]+1;
				  	strcpy(currstr,currstr+1);
				  	indptr++;
				  	if (indptr > indlen/sizeof(long))
				  	{
					  	printf("Index table overflow. Dictionary too large?\n");
					  	exit(1);
				  	}
				  }
				  if (currstr[0] < 128)
				  {
					  for (isc = 0; isc <= excount; isc++)
					  {
						  if (( exlens[isc] == strlen(currstr)) &&
						  (stringcomp(currstr,exlist[isc]) == 0)   )
						  {
							  indptr--;
							  break;
						  }
					  }
				  }
			  }
		  }
	  }
	  else
	  {
		  if (alphaoreuc(c) || c == SPTAG)
		  {
			  inwd = TRUE;
			  jindex[indptr] = schi;
			  cstrp = 1;
			  currstr[0] = c;
			  currstr[1] = '\0';
			  saving = TRUE;
		  }
	  }
    }
    indptr--;
    printf("Index entries: %ld  \nSorting (this is slow)......\n",indptr);
    jqsort(llone,indptr);
    printf("Sorted\nWriting index file ....\n");
    fp = fopen(JDXname,"wb");
    if (fp==NULL )
    {
    printf("\nCannot open %s output file\n",JDXname);
    exit(1);
  }
  jindex[0] = diclen+jiver;
  fwrite(jindex,sizeof(long),indptr+1,fp);
  i = fclose(fp);
  if (i != 0)
  {
		printf("\nDictionary Index File Close Failure\n");
		exit(1);
  }
  exit (0);
}
/*======function to sort jindex table====================*/
void jqsort(long lhs, long rhs)
{
	long i,last,midp;
	unsigned long temp;
	if (lhs >= rhs) return;
	/* Swap ( lhs , (lhs+rhs)/2);*/
	midp = (lhs+rhs)/2;
	temp = jindex[lhs];
	jindex[lhs] = jindex[midp];
	jindex[midp] = temp;
	last = lhs;
	for (i = lhs+1;i <= rhs; i++)
		{
			if (Kstrcmp(jindex[i],jindex[lhs]) < 0)
			{
				/* Swap(++last,i);*/
				last++;
				temp = jindex[i];
				jindex[i] = jindex[last];
				jindex[last] = temp;
			}
		}
/*	Swap (lhs,last);*/
	temp = jindex[lhs];
	jindex[lhs] = jindex[last];
	jindex[last] = temp;
	jqsort(lhs,last-1);
	jqsort(last+1,rhs);
}
/*=====string comparison used by jqsort==========================*/
int Kstrcmp(unsigned long lhs, unsigned long rhs)
{
	int i,c1,c2;
/* effectively does a strnicmp on two "strings" within the dictionary,
   except it will make katakana and hirgana match (EUC A4 & A5) */

	for (i = 0; i<20 ; i++)
	{
		c1 = db[lhs+i];
		c2 = db[rhs+i];
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
/*=====xjdicrc - access and analyze "xjdicrc" file (if any)==============*/
void xjdicrc()
{
	unsigned char xjdicdir[128],rcstr[80],*rcwd;
	int iex;
	FILE *fm,*fopen();

	iex = 0;
	xjdicdir[0] = '\0';
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
	if (strlen(ENVname) > 2)
	{
		strcpy(xjdicdir,ENVname);
		strcat(xjdicdir,"/");
	}
	else    
	{
		strcpy(xjdicdir,(unsigned char *)getenv("HOME"));
		strcat(xjdicdir,"/");
	}

	strcat(xjdicdir,ctl_file);
	fm = fopen(xjdicdir,"r");
	if (fm == NULL)
	{
		strcpy(xjdicdir,ctl_file);
		fm = fopen(xjdicdir,"r");
	}
	if (fm != NULL)
	{
		while(fgets(rcstr,79,fm) != NULL)
		{
			rcwd = (unsigned char *)strtok(rcstr," \t");
                        if( stringcomp((unsigned char *)"exlist",rcwd) == 0)
                        {
				while (TRUE)
				{
                                	rcwd = (unsigned char *)strtok(NULL," \t\f\r\n");
					if (rcwd == NULL) break;
					strcpy(exlist[iex],rcwd);
					exlens[iex] = strlen(rcwd);
					if (iex < EXLIM) iex++;
				}
				excount = iex-1;
                                continue;
                        }
		}
	}
	if (fm == NULL)
	{
		printf("No control file detected!\n");
		return;
	}
	else
	{
		fclose(fm);
		return;
	}
}
/*=======function to test a character for alpha or kana/kanji====*/
int alphaoreuc(unsigned char x)
{
	int c;

	c = x & 0xff;
	if(((c >= 65) && (c <= 90)) || ((c >= 97) && (c <= 122)))
	{
		return (TRUE);
	}
	if ((c >= '0') && (c <= '9'))
	{
		return(TRUE);
	}
	if ((c & 0x80) > 0)
	{
		return(TRUE);
	}
	return (FALSE);
}

