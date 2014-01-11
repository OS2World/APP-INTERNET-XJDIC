/**************************************************************************
*                          X  J  D  S  A                                  *
*                                                                         *
*            This is the bit that emulates a server for the stand-alone   *
*            version                                                      *
*                                                                         *
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
#include "xjdic.h"

unsigned char Dnamet[10][100],XJDXnamet[10][100];
unsigned char CBname[100];
unsigned char *dicbufft[10];
unsigned long diclent[10], indlent[10],indptrt[10];
int NoDics,CurrDic;
int iterlimit;

/* extern int TRIGGER; */

void xjdserver (int type, int dic_no, long index_posn, int sch_str_len, 
		unsigned char *sch_str, int *sch_resp, long *res_index, 
		int *hit_posn, int *res_len, unsigned char *res_str,
		long *dic_loc );


/*===xjserver===front-end routine for the dictionary lookup engine========*/

void xjdserver (int type, int dic_no, long index_posn, int sch_str_len, 
		unsigned char *sch_str, int *sch_resp, long *res_index, 
		int *hit_posn, int *res_len, unsigned char *res_str,
		long *dic_loc )
/*
	This function handles all access to the dictionary files and indices.
	The accesses have been consolidated here to cater for an alternative
	function which makes requests on a server.

	If called with type == XJ_FIND, it searches in the indicated dictionary
	for the first occurrence of the matching string, and returns the entry
	and its location, Return code is XJ_OK.
	If called with type == XJ_ENTRY, it returns the entry and its location,
	provided that entry matches the string.
	If called with type == XJ_GET, it returns the entry and its location.
	All failing calls result in a return code of XJ_NBG.

*/
{
	long lo, hi, itok, lo2, hi2, schix, schiy;
	extern long it;
	int res, i;

	hi = indptrt[dic_no];

	if (type == XJ_FIND)
	{
		lo = 1;
		iterlimit = MAXITER;
		while(TRUE)
		{
			if (!iterlimit--) break;
  			it = (lo+hi)/2;
/* if (TRIGGER) printf("Calling KSTRCMP - 1\n"); */
			res = Kstrcmp(sch_str_len,sch_str);
			if (res == 0)
			{
				itok = it;
				lo2 = lo;
				hi2 = it;
				while (TRUE)
				{
					if(lo2+1 >= hi2) break;
					it = (lo2+hi2)/2;
/* if (TRIGGER) printf("Calling KSTRCMP - 1.5\n"); */
					res = Kstrcmp(sch_str_len,sch_str);
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
			*sch_resp = XJ_NBG;
			return;
		}
/* as the above sometimes misses the first matching entry, step back to the
    first  */
		while (TRUE)
		{
/* if (TRIGGER) printf("Calling KSTRCMP - 2\n"); */
			if(Kstrcmp(sch_str_len,sch_str) == 0)
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

	if (type == XJ_ENTRY)
	{
		if (index_posn > hi)
		{
			*sch_resp = XJ_NBG;
			return;
		}
		it = index_posn;
/* if (TRIGGER) printf("Calling KSTRCMP - 3\n"); */
		res = Kstrcmp(sch_str_len,sch_str);
		if (res != 0)
		{
			*sch_resp = XJ_NBG;
			return;
		}
	}
	if (type == XJ_GET)
	{
		if (index_posn > hi)
		{
			*sch_resp = XJ_NBG;
			return;
		}
		it = index_posn;
	}

/*  Common code to set up the return parameters for both call types  */
	schix = jindex(it);
	schiy = schix;
	*res_index = it;
/* back off to the start of this line   */
	while ((dbchar(schix) != 0x0a) && (schix >= 0)) schix--;
	schix++;
	*hit_posn = schiy - schix;
	*dic_loc = schix;
	for (i = 0; dbchar(schix+i) != 0x0a; i++)
	{
		if (i == 512)
		{
			printf ("Reply overrun\n");
			exit(1);
		}
		res_str[i] = dbchar(schix+i);
	}
	res_str[i+0] = 0x0a; /* NL tells user s/w that it is the end of an entry */
	res_str[i+1] = 0;
	*res_len = strlen(res_str);
/* if (TRIGGER) printf("STR: %s\n",res_str); */
	*sch_resp = XJ_OK;
	return;
}
