/**************************************************************************
*                 X  J  D  C  L  I  E  N  T                               *     *
*              Code  for Interfacing the Client with the server           *
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

/* for Solaris 2.5, which doesn't have INADDR_NONE in its <netinet/in.h> */
#ifdef SOLARIS
#define INADDR_NONE -1
#endif


#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <stdlib.h>
#include <unistd.h>
#include <signal.h>
#include "xjdic.h"

#define CVERBOSE 0
int chk_cnt=0;
extern int errno;
unsigned char host[51] = {"localhost"};
unsigned char yn[2];
unsigned int portno = XJ_PORTNO;
char protocol[4] = {"udp"};
int s, elapse;
struct timeval timeout;
int txno = 0;

REQ_PDU pdu_out;
RSP_PDU pdu_in;
int pduseq = 0;
int curr_timer = TINITVAL;
int rep_count;
struct timezone tz;
long timeofday_st,timeofday_en;
fd_set fildesc;
int nfds;
unsigned char *sptr;
int NoDics,CurrDic;
char Dnamet[10][100];

void xjdserver (int type, int dic_no, long index_posn, int sch_str_len,
                unsigned char *sch_str, int *sch_resp, long *res_index, 
                int *hit_posn, int *res_len, unsigned char *res_str,
                long *dic_loc );
void DicSet();
int connectsock(int portno, char *host);
void reqchecksum();
int respchecksum();

void DicSet()
{
/*	In the Client version, DicSet() establishes the connection with 
	the server. */

	int i,schresp, dumint, trying,hullodic;
	long dumlong,dumlong0 = 0;
	char dummy[2],dnamelist[512];

	connectsock(portno, host);
	nfds = getdtablesize();
	FD_SET(s, &fildesc);
	trying = TRUE;
	while (trying)
	{
		xjdserver(XJ_HULLO, 0, dumlong0, 0, dummy, &schresp, &dumlong, 
			&hullodic, &dumint, dnamelist, &dumlong);
		if (schresp == XJ_OK) 
		{
			printf("Server: %s detected\n", host);
			NoDics = hullodic;
			sptr = strtok(dnamelist,"#");
			while (sptr != NULL)
			{
				i = sptr[0] - '0';
				if (i <= NoDics) 
				{
					strcpy(Dnamet[i],sptr+1);
					printf ("Dictionary: %d [%s]\n",i,Dnamet[i]);
				}
				sptr = strtok(NULL,"#");
			}
			CurrDic = 1;
			return;
		}
		printf("Server not responding.(%d) Try again? (y/n)",schresp);
		scanf("%c",dummy);
		printf("\n");
		if ((dummy[0] | 0x20) == 'n') exit(1);
	}
}

int connectsock(int portno, char *host)
{

	struct protoent *ppe;
	struct hostent *phe;
	struct sockaddr_in sin;

	bzero((char *)&sin, sizeof(sin));
	sin.sin_family = AF_INET;
	sin.sin_port = htons(portno);
	if (phe = gethostbyname(host))
		bcopy(phe->h_addr, (char *)&sin.sin_addr, phe->h_length);
	else if ((sin.sin_addr.s_addr = inet_addr(host)) == INADDR_NONE)
	{
		printf ("Cannot Get Host Entry!!\n");
		exit(1);
	}
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
	if (connect (s, (struct sockaddr *)&sin, sizeof(sin)) < 0)
	{
		printf ("Cannot connect to host: %s, port: %d\n",host,portno);
		exit(1);
	}

	return (s);
}

int respchecksum()
{
	long temp;
	int i;
	char yn[5];

	if (CVERBOSE) printf("PDU: %d %d %d %d %d %d %s %d\n",
	       ntohs(pdu_in.xjdrsp_type),
	       ntohs(pdu_in.xjdrsp_seq),
	       ntohl(pdu_in.xjdrsp_resindex),
	       ntohl(pdu_in.xjdrsp_dicloc),
	       ntohs(pdu_in.xjdrsp_hitposn),
	       ntohs(pdu_in.xjdrsp_reslen),
	       pdu_in.xjdrsp_resstr,
	       ntohl(pdu_in.xjdrsp_checksum));
	temp = ntohs(pdu_in.xjdrsp_type);
	temp+= ntohs(pdu_in.xjdrsp_seq);
	temp+= ntohl(pdu_in.xjdrsp_resindex);
	temp+= ntohl(pdu_in.xjdrsp_dicloc);
	temp+= ntohs(pdu_in.xjdrsp_hitposn);
	temp+= ntohs(pdu_in.xjdrsp_reslen);
	for (i = 0; i < strlen(pdu_in.xjdrsp_resstr); i++)
		temp+= pdu_in.xjdrsp_resstr[i];
	if (ntohl(pdu_in.xjdrsp_checksum) == temp) 
	{
		chk_cnt = 0;
		return (TRUE);
	}
	if (CVERBOSE) printf("Cal checksum: %d PDU checksum: %d\n",temp,ntohl(pdu_in.xjdrsp_checksum));
	if (chk_cnt++ > 20)
	{
		printf("20 consecutive checksum failures: Try again? ");
		scanf("%s",&yn);
		printf("\n");
		if((yn[0] | 0x20) == 'y') 
		{
			chk_cnt = 0;
			return(FALSE);
		}
		else 
		{
			exit(1);
		}
	}
	return (FALSE);
}

void reqchecksum()
{
	long temp;
	int i;

	temp = ntohs(pdu_out.xjdreq_type);
	temp+= ntohs(pdu_out.xjdreq_seq);
	temp+= ntohs(pdu_out.xjdreq_dicno);
	temp+= ntohl(pdu_out.xjdreq_indexpos);
	temp+= ntohs(pdu_out.xjdreq_schlen);
	for (i = 0; i < strlen(pdu_out.xjdreq_schstr); i++) temp+= pdu_out.xjdreq_schstr[i];

	pdu_out.xjdreq_checksum = htonl(temp);
}

void xjdserver (int type, int dic_no, long index_posn, int sch_str_len,
                unsigned char *sch_str, int *sch_resp, long *res_index, 
                int *hit_posn, int *res_len, unsigned char *res_str,
                long *dic_loc )
{
	int i, ares, sendit;

	gettimeofday((struct timeval *)&timeout,(struct timezone *)&tz);
	timeofday_st = timeout.tv_sec;
	pdu_out.xjdreq_type = htons(type);
	pdu_out.xjdreq_seq = htons(++pduseq);
	pdu_out.xjdreq_dicno = htons(dic_no);
	pdu_out.xjdreq_indexpos = htonl(index_posn);
	pdu_out.xjdreq_schlen = htons(sch_str_len);
	strcpy(pdu_out.xjdreq_schstr,sch_str);
	reqchecksum();
	sendit = TRUE;
	while (TRUE)
	{
		timeout.tv_sec = curr_timer;
		timeout.tv_usec = 0;
		if (sendit) 
		{
			txno++;
			(void) write (s, &pdu_out,sizeof(REQ_PDU));
			if (CVERBOSE) printf("txno %d (seq: %d)\n",txno,pduseq);
		}
		if ((ares = select(nfds, &fildesc, (fd_set *)0, (fd_set *)0, (struct timeval *)&timeout) )< 0)
		{
			printf("Select error: %s\n", strerror(errno));
			exit(1);
		}
		sendit = TRUE; 
		if (ares == 0)
		{
			if (CVERBOSE) printf("Timeout: %d secs (seq: %d)\n",curr_timer,pduseq);
			FD_SET(s, &fildesc);
			if (rep_count < TMAXREP) 
			{
				rep_count++;		
				continue;
			}
			else
			{
				if (curr_timer >= TMAXVAL)
				{
					rep_count = 0;
					printf("Cannot contact Server: %s Try again? ",host);
					scanf("%s",&yn);
					printf("\n");
					if((yn[0] | 0x20) == 'y') 
					{
						curr_timer = TINITVAL;
						continue; 
					}
					else 
					{
						exit(1);
					}
				}
				else
				{
					curr_timer*=2;
					rep_count = 0;
					continue;
				}
			}
		}
		if (CVERBOSE) printf("Something in!\n");
		gettimeofday((struct timeval *)&timeout,(struct timezone *)&tz);
		timeofday_en = timeout.tv_sec;
		elapse = timeofday_en - timeofday_st;
		if (elapse < 1) elapse = 1;
		if (elapse > curr_timer) 
		{
			curr_timer = elapse << 1;
		}
		else
		{
			if (curr_timer - elapse > 2) curr_timer = elapse+2;
		}
		if (recv(s, &pdu_in, sizeof(RSP_PDU), 0) < 0)
		{
			if (errno == 111)
			{
				printf("Cannot contact Server: %s Try again?\n",host);
				scanf("%s",&yn);
				if((yn[0] | 0x20) == 'y') 
				{
					continue; 
				}
				else 
				{
					exit(1);
				}
			}
			printf("UDP recv error: %d %s\n",errno,strerror(errno));
			exit(1);
		}
		if (!respchecksum()) 
		{
			if (CVERBOSE) printf("PDU checksum error (seq: %d)\n",pduseq);
			continue;
		}
		if (ntohs(pdu_in.xjdrsp_seq) != pduseq) 
		{
			if (CVERBOSE) printf("PDU sequence error. Rec: %d Exp: %d\n",ntohs(pdu_in.xjdrsp_seq),pduseq);
			sendit = FALSE;
			continue;
		}
		if (CVERBOSE) printf("Valid PDU: %d %ld %d %d\n",ntohs(pdu_in.xjdrsp_type),
							ntohl(pdu_in.xjdrsp_resindex),
							ntohs(pdu_in.xjdrsp_hitposn),
							ntohs(pdu_in.xjdrsp_reslen));
		*sch_resp = ntohs(pdu_in.xjdrsp_type);
		*res_index = ntohl(pdu_in.xjdrsp_resindex);
		*hit_posn = ntohs(pdu_in.xjdrsp_hitposn);
		*res_len = ntohs(pdu_in.xjdrsp_reslen);
		*dic_loc = ntohl(pdu_in.xjdrsp_dicloc);
		for (i = 0; i < *res_len; i++) 
		{
		
			res_str[i] = pdu_in.xjdrsp_resstr[i];
			res_str[i+1] = 0;
		}
		return;
	}


}
