########################################################################
#
#       X J D I C
#
#######################################################################
# This is the makefile for xjdic/xjdserver/xjdxgen V2.4
# 
# to use this file, you have several options:
#	make all - does all the binaries
#	make client - just makes the xjdic_cl binary
#	make server - just makes the xjdserver server
#	make stand - just makes the xjdic_sa stand-alone version
#	make xjdxgen - just makes the xjdxgen index generator
#	make exjdxgen - just makes the exjdxgen extension file index generator
#	make clean - just tidies up, removing the .o files.
#	make realclean - deletes everything compiled, not just .o files.
#
#	This Makefile is set to use the gcc compiler. If you want cc instead
#	you will need to alter the "CC=gcc" below, or use CC=cc on the command 
#	line.
#
#	If you want strict BSD ioctls used (which seems to be the case
#	for Suns) add -D__STRICT_BSD___ to the SACFLAGS and CLCFLAGS macros.
#
#	You need to select one of three dictionary and index file
#	access options by uncommenting the appropriate SACFLAGS and
#	SVCFLAGS macros:
#
#		memory-mapped I/O	use -DMMAP
#		demand-paging		use -DDEMAND_PAGING
#		load into RAM		use -DRAM_LOAD
#
#	Memory-mapped I/O does not appear to function correctly
#	under Ultrix. It works with Solaris and Linux.
#
#	Note that it is assumed that window-size ioctls are available.
#	If you want to use curses instead, delete the -DWINSIZE....,
#	and compile the client and/or the stand-alone programs with
#	the "-lcurses -ltermcap".
#
#	Expect some compilation warnings about "qsort". No-one seems
#	able to remove them.
#
#	For DEC Ultrix, you will probably need to alter the comments
#	on the SACFLAGS and SVCFLAGS macros to remove MMAP, as this
#	appears not to work on that OS.
#
#	For Sun and Linux, you may need to include the "unistd.h" file.
#
#	For Solaris 2.x, you will probably need to uncomment the following
#	if you want to use the server/client operation. Also be prepared
#	for some complaining about pointer mismatches in routines like
#	`recv'. They can be ignored.
#
#LIBS= -lsocket -lnsl
#
CC=gcc -g
all: xjdic_sa xjdic_cl xjdserver xjdxgen exjdxgen
client: xjdic_cl
server: xjdserver
stand: xjdic_sa
#
#	X J D X G E N
#
JDXOBJECTS = xjdxgen.o
xjdxgen: $(JDXOBJECTS)
	$(CC) $(JDXOBJECTS) -o xjdxgen
xjdxgen.o:	xjdxgen.c
	$(CC) -c xjdxgen.c
#
#	E X J D X G E N
#
EJDXOBJECTS = exjdxgen.o
exjdxgen: $(EJDXOBJECTS)
	$(CC) $(EJDXOBJECTS) -o exjdxgen
exjdxgen.o:	exjdxgen.c
	$(CC) -c exjdxgen.c
#
#	S T A N D _ A L O N E 
#
SAOBJECTS = xjdsa.o xjdcomm_sa.o xjdservcomm_sa.o xjdfrontend_sa.o
#SACFLAGS = -DXJDFRONTEND -DXJDDIC -DDEMAND_PAGING
SACFLAGS = -DXJDFRONTEND -DXJDDIC -DMMAP
#SACFLAGS = -DXJDFRONTEND -DXJDDIC -DRAM_LOAD
xjdic_sa: $(SAOBJECTS)
	$(CC) $(SAOBJECTS) -o xjdic_sa
xjdsa.o: xjdsa.c
	$(CC) -c $(SACFLAGS) xjdsa.c
xjdcomm_sa.o: xjdcomm.c
	$(CC) -c $(SACFLAGS) xjdcomm.c -o xjdcomm_sa.o
xjdservcomm_sa.o: xjdservcomm.c
	$(CC) -c $(SACFLAGS) xjdservcomm.c -o xjdservcomm_sa.o
xjdfrontend_sa.o: xjdfrontend.c
	$(CC) -c $(SACFLAGS) xjdfrontend.c -o xjdfrontend_sa.o
$(SAOBJECTS): xjdic.h
#
#	C L I E N T
#
CLOBJECTS = xjdclient.o xjdcomm_cl.o xjdfrontend_cl.o
CLCFLAGS = -DXJDFRONTEND -DXJDCLSERV
xjdic_cl: $(CLOBJECTS)
	$(CC) $(CLOBJECTS) $(LIBS) -o xjdic_cl
xjdclient.o: xjdclient.c
	$(CC) -c $(CLCFLAGS) xjdclient.c
xjdcomm_cl.o: xjdcomm.c
	$(CC) -c $(CLCFLAGS) xjdcomm.c -o xjdcomm_cl.o
xjdfrontend_cl.o: xjdfrontend.c
	$(CC) -c $(CLCFLAGS) xjdfrontend.c -o xjdfrontend_cl.o
$(CLOBJECTS): xjdic.h
#
#	S E R V E R
#
SVOBJECTS = xjdcomm_sv.o xjdservcomm_sv.o xjdserver.o
#SVCFLAGS = -DXJDDIC -DXJDCLSERV -DDEMAND_PAGING
SVCFLAGS = -DXJDDIC -DXJDCLSERV -DMMAP
#SVCFLAGS = -DXJDDIC -DXJDCLSERV -DRAM_LOAD
xjdserver: $(SVOBJECTS)
	$(CC) $(SVOBJECTS) $(LIBS) -o xjdserver
xjdcomm_sv.o: xjdcomm.c
	$(CC) -c $(SVCFLAGS) xjdcomm.c -o xjdcomm_sv.o
xjdservcomm_sv.o: xjdservcomm.c
	$(CC) -c $(SVCFLAGS) xjdservcomm.c -o xjdservcomm_sv.o
xjdserver.o: xjdserver.c
	$(CC) -c $(SVCFLAGS) xjdserver.c 
$(SVOBJECTS): xjdic.h
#
clean:
	rm -f *.o
realclean: clean
	rm -f xjdic_sa xjdic_cl xjdserver xjdxgen exjdxgen
#
#    This program is free software; you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation; either version 1, or (at your option)
#    any later version.
#
#    This program is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License
#    along with this program; if not, write to the Free Software
#    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.     */
