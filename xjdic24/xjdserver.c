/**************************************************************************
*                 X  J  D  S E R V E R                                    *
*              Dictionary Server Program                                  *
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
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <stdlib.h>
#include <signal.h>
#include "xjdic.h"

#define SVERBOSE 0

void xjdicrc();
void DicSet ();
unsigned char *DicName(int dn);

int portno=XJ_PORTNO;
int DontFork = FALSE;
int alen;
char host[51];

REQ_PDU pdu_in;
RSP_PDU pdu_out;

struct sockaddr_in fsin;
int sock;

long lo, hi, itok, lo2, hi2, schix, schiy;
int res, i;
long it;
unsigned char ENVname[50];
unsigned char cl_rcfile[100];
int jiver = 14; 
int thisdic = 0;
int DicNum;

extern int errno;

extern unsigned char Dnamet[10][100],XJDXnamet[10][100];
extern unsigned char *dicbufft[10];
extern unsigned long diclent[10], indlent[10],indptrt[10];
extern int NoDics,CurrDic;

char DicDir[100];

int passiveUDP(int portno)
{
	struct protoent *ppe;
	struct sockaddr_in sin;
	int s;

	bzero((char *)&sin, sizeof(sin));
	sin.sin_family = AF_INET;
	sin.sin_addr.s_addr = INADDR_ANY;
	sin.sin_port = htons(portno);
	if ((ppe = getprotobyname("udp")) == 0)
	{
		printf ("Cannot set up UDP!!\n");
		exit(1);
	}
	s = socket(PF_INET, SOCK_DGRAM, ppe->p_proto);
	if (s < 0)
	{
		printf ("Cannot create socket!!: %s\n",strerror(errno));
		exit(1);
	}
	if (bind(s, (struct sockaddr *)&sin, sizeof(sin)) < 0)
	{
		printf ("Cannot bind to port: %d\n",portno);
		exit(1);
	}

	return (s);
}

int checksum_in()
{
	long temp;

	temp = ntohs(pdu_in.xjdreq_type);
	temp+= ntohs(pdu_in.xjdreq_seq);
	temp+= ntohs(pdu_in.xjdreq_dicno);
	temp+= ntohl(pdu_in.xjdreq_indexpos);
	temp+= ntohs(pdu_in.xjdreq_schlen);
	for (i = 0; i < strlen(pdu_in.xjdreq_schstr); i++) temp+= pdu_in.xjdreq_schstr[i];

	if (temp == ntohl(pdu_in.xjdreq_checksum)) return(TRUE);
	return(FALSE);
}

void sendresponse()
{
	long temp;

	temp = ntohs(pdu_out.xjdrsp_type);
	temp+= ntohs(pdu_out.xjdrsp_seq);
	temp+= ntohl(pdu_out.xjdrsp_resindex);
	temp+= ntohl(pdu_out.xjdrsp_dicloc);
	temp+= ntohs(pdu_out.xjdrsp_hitposn);
	temp+= ntohs(pdu_out.xjdrsp_reslen);
	for (i = 0; i < strlen(pdu_out.xjdrsp_resstr); i++)
		temp+= pdu_out.xjdrsp_resstr[i];
	pdu_out.xjdrsp_checksum = htonl(temp);
	if (SVERBOSE) printf("PDU sent: %d %d %d %d %d %d %s %d\n",
			ntohs(pdu_out.xjdrsp_type),
			ntohs(pdu_out.xjdrsp_seq),
			ntohl(pdu_out.xjdrsp_resindex),
			ntohl(pdu_out.xjdrsp_dicloc),
			ntohs(pdu_out.xjdrsp_hitposn),
			ntohs(pdu_out.xjdrsp_reslen),
			pdu_out.xjdrsp_resstr,
			temp);
	i = sendto (sock, (RSP_PDU *) &pdu_out, sizeof(pdu_out)-512+strlen(pdu_out.xjdrsp_resstr)+1,
			0, (struct sockaddr *)&fsin, sizeof(fsin));
	if (i < 0)
	{
		printf ("sendto error!: %s\n",strerror(errno));
	}
}

/*                  M A I N                                      */

main(argc,argv)
int argc;
unsigned char **argv;

{
	int iterlimit,i;
  	unsigned char *dicenv,strtmp[50];
	unsigned char xap[50];

	
  	printf("XJDSERVER Version %s (Japanese Dictionary Server) Copyright J.W.Breen 2003.\n",SVER);

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
        strcpy (Dnamet[0], "kanjidic");
        strcpy (Dnamet[1], "edict");
        strcpy (XJDXnamet[0], "kanjidic.xjdx");
	strcpy (XJDXnamet[1], "edict.xjdx");
	NoDics = 1;
	cl_rcfile[0] = 0;
/* process command-line options*/
	if (argc > 1)
	{
		for (i = 1; i < argc; i++)
		{
			strcpy(xap,argv[i]);
			if ((xap[0] == '-') && (xap[1] == 'h'))
			{
				printf("Command-line options:\n");
				printf("\t -c control_file\n");
				printf("\t -K (do not create daemon)\n");
				printf("\t -P nnnn (use UDP port nnnn\n");
				printf("\t -k kanji_dic_file\n");
				printf("\t -d dictionary_file (up to 9)\n");
				printf("\t -h (this information)\n");
				exit(0);
			}
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
				printf("Command-line request to use dictionary files: %s and %s\n",Dnamet[thisdic],XJDXnamet[thisdic]);
				continue;
			}
			if ((xap[0] == '-') && (xap[1] == 'K'))
			{
				DontFork = TRUE;
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
		}
	}
	xjdicrc();
  	printf ("Loading Dictionary and Index files.  Please wait...\n");
/* printf("TEST! NoDics = %d\n",NoDics); */
/* for(i = 0;i <= NoDics; i++) printf("TEST! Dnamet[] = %s\n",Dnamet[i]); */
	if (!DontFork)
	{
		i = fork();
		if (i < 0)
		{
			printf("error when forking: %s\n",strerror(errno));
			exit(1);
		}
		if (i) exit(0);
	}
  	DicSet ();
	sock = passiveUDP(portno);
	printf ("Server Loaded & Ready\n");
/*
	From here on, the code loops endlessly, reading  requests from the
	UDP port, looking up the dictionary, and sending back the answers.
*/
  	while (TRUE)
	{
		alen = sizeof(fsin);
		if (recvfrom(sock, (REQ_PDU *) &pdu_in, sizeof(pdu_in), 0, 
			(struct sockaddr *)&fsin, &alen) < 0)
		{
			fprintf (stderr,"recvfrom failure: %s\n",strerror(errno));
			continue;
		}

		if (!checksum_in) continue; 	/* ignore requests with bad checksums*/
		pdu_out.xjdrsp_seq = pdu_in.xjdreq_seq;
		pdu_out.xjdrsp_resindex = htonl(0);
		pdu_out.xjdrsp_dicloc = htonl(0);
		pdu_out.xjdrsp_hitposn = htons(0);
		pdu_out.xjdrsp_reslen= htons(0);
		pdu_out.xjdrsp_resstr[0] = 0;
		pdu_in.xjdreq_type = ntohs(pdu_in.xjdreq_type);
		pdu_in.xjdreq_dicno = ntohs(pdu_in.xjdreq_dicno);
		pdu_in.xjdreq_schlen = ntohs(pdu_in.xjdreq_schlen);
		pdu_in.xjdreq_indexpos = ntohl(pdu_in.xjdreq_indexpos);


		/* printf ("PDU: %d received\n",pdu_in.xjdreq_type);*/
		if (pdu_in.xjdreq_type == XJ_HULLO)
		{
			pdu_out.xjdrsp_type = htons(XJ_OK);
			pdu_out.xjdrsp_hitposn = htons(NoDics);
			pdu_out.xjdrsp_resstr[0] = 0;
			for (i = 0; i<=NoDics;i++)
			{
				sprintf(strtmp,"#%d%s",i,DicName(i));
				strcat(pdu_out.xjdrsp_resstr,strtmp);
			}
			pdu_out.xjdrsp_reslen = htons(strlen(pdu_out.xjdrsp_resstr));
			sendresponse();
			continue;
		}

		if (pdu_in.xjdreq_dicno > NoDics)
		{
			pdu_out.xjdrsp_type = htons(XJ_PROTERR);
			sendresponse();
			continue;
		}
		DicNum = pdu_in.xjdreq_dicno;
		hi = indptrt[pdu_in.xjdreq_dicno];

		if (pdu_in.xjdreq_type == XJ_FIND)
		{
			lo = 1;
			iterlimit = MAXITER;
			while(TRUE)
			{
				if (!iterlimit--) break;
  				it = (lo+hi)/2;
				res = Kstrcmp(pdu_in.xjdreq_schlen,pdu_in.xjdreq_schstr);
				if (res == 0)
				{
					itok = it;
					lo2 = lo;
					hi2 = it;
					while (TRUE)
					{
						if(lo2+1 >= hi2) break;
						it = (lo2+hi2)/2;
						res = Kstrcmp(pdu_in.xjdreq_schlen,pdu_in.xjdreq_schstr);
						if (res == 0)
						{
							hi2 = it;
							itok = it;
							continue;
						}
						else
						{
							lo2 = it+1;
						}
					}
					it = itok;
					res = 0;
					break;
				}
				if (res < 0)
				{
					hi = it-1;
				}
				else
				{
					lo = it+1;
				}
				if (lo > hi) break;
			}
			if (res != 0)
			{
				pdu_out.xjdrsp_type = htons(XJ_NBG);
				sendresponse();
				continue;
			}
	/* as the above sometimes misses the first matching entry, step back to the
    	first  */
			while (TRUE)
			{
				if(Kstrcmp(pdu_in.xjdreq_schlen,pdu_in.xjdreq_schstr) == 0)
				{
					it--;
					if (it == 0)
					{
						it = 1;
						break;
					}
					continue;
				}
				else
				{
					it++;
					break;
				}
			}
		}
	
	/*	Get next entry. Check (a) if the caller hasn't gone off the end of the
		table, and (b) if the (next) entry matches.		*/
	
		if (pdu_in.xjdreq_type == XJ_ENTRY)
		{
			if (pdu_in.xjdreq_indexpos > hi)
			{
				pdu_out.xjdrsp_type = htons(XJ_NBG);
				sendresponse();
				continue;
			}
			it = pdu_in.xjdreq_indexpos;
			res = Kstrcmp(pdu_in.xjdreq_schlen,pdu_in.xjdreq_schstr);
			if (res != 0)
			{
				pdu_out.xjdrsp_type = htons(XJ_NBG);
				sendresponse();
				continue;
			}
		}
		if (pdu_in.xjdreq_type == XJ_GET)
		{
			if (pdu_in.xjdreq_indexpos > hi)
			{
				pdu_out.xjdrsp_type = htons(XJ_NBG);
				sendresponse();
				continue;
			}
			it = pdu_in.xjdreq_indexpos;
		}
	
	/*  Common code to set up the return parameters for both call types  */
		schix = jindex(it);
		schiy = schix;
		pdu_out.xjdrsp_resindex = htonl(it);
	/* back off to the start of this line   */
		while ((dbchar(schix) != 0x0a) && (schix >= 0)) schix--;
		schix++;
		pdu_out.xjdrsp_dicloc = htonl(schix);
		pdu_out.xjdrsp_hitposn = htons(schiy - schix);
		if (pdu_in.xjdreq_type == XJ_ENTRY)
		{
			pdu_out.xjdrsp_resindex = htonl(schix);
		}
		if (pdu_in.xjdreq_type == XJ_GET)
		{
			pdu_out.xjdrsp_resindex = htonl(schix);
		}
		for (i = 0; dbchar(schix+i) != 0x0a; i++)
		{
			pdu_out.xjdrsp_resstr[i] = dbchar(schix+i);
		}
		pdu_out.xjdrsp_resstr[i+0] = 0x0a; /* NL tells user s/w that it is the end of an entry */
		pdu_out.xjdrsp_resstr[i+1] = 0;
		pdu_out.xjdrsp_reslen = htons(strlen(pdu_out.xjdrsp_resstr));
		pdu_out.xjdrsp_type = htons(XJ_OK);
		sendresponse();
		continue;
	}
}
