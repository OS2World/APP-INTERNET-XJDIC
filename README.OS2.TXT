README.OS2 FOR XJDIC V2.4 
| Release 5 (2009-06-30)

  XJDIC is a text-mode Japanese/English dictionary program (written by Jim
  Breen), designed to use the freeware EDICT and KANJIDIC dictionaries.  This
  is an OS/2 port of version 2.4, built using klibc and GCC 3.3.5 revision 3.

  XJDIC outputs Japanese text in both kanji and hiragana/katakana.  It does NOT
  output in romaji (although it does support romaji input).  If you cannot read
  at least hiragana and katakana, this program will likely be of little use to 
  you.

  For obvious reasons, XJDIC must be run in an environment capable of displaying
  Japanese characters in a console (such as provided by the KShell utility).
  XJDIC supports output in several encoding formats, including ISO-2022-JP, 
  Shift-JIS, and EUC-JP.

  You will require the following in order to run this build of XJDIC:
   - The kLIBC 0.6.3 runtime (LIBC063.DLL).
   - Jim Breen's EDICT and KANJIDIC files (see the 'INSTALLATION' section').
  
  If you are not running the Japanese DBCS version of OS/2, you will also need:
   - KO Myung-hun's KShell program.
   - A monospaced font with Japanese support.
  See the 'RUNNING THE PROGRAM' section for more information on both of these.


FILES INCLUDED

  xjdic_sa.exe      - XJDIC program (standalone version).
  xjdic_cl.exe      - XJDIC client program (for client-server version).
  xjdserver.exe     - XJDIC server program (for client-server version).
  xjdxgen.exe       - Index generator for EDICT and KANJIDIC dictionaries.
  exjdxgen.exe      - Index generator for optional EDICTEXT dictionary.
  xjdrad.exe        - Kanji radical lister (displays output in EUC-JP).
  .xjdicrc.skel     - Sample control file.
  gnu_licence       - Program license terms.
  kanjstroke        - File containing kanji stroke-count information.
  radicals.tm       - File containing bushu numbers and descriptive kanji.
  radkfile          - File containing kanji radical information.
  romkana.cnv       - Kana conversion information for romaji input mode.
  vconj             - Verb/adjective conjugation information for lookups.
  xjdic.1           - Unix-style manual page.
  xjdic22.WHATSNEW  - Release notes for version 2.2.
  xjdic23.WHATSNEW  - Release notes for version 2.3.
  xjdic24.WHATSNEW  - Release notes for version 2.4.
  xjdic24.inf       - Program documentation (this is plain text, not OS/2 INF).
  xjdic24.install   - Original installation instructions (for Unix systems).
  xjdrad.txt        - Output from xjdrad.exe, converted to Shift-JIS.
  README.OS2        - This file.


INSTALLATION

  --------------------------------- IMPORTANT ----------------------------------
  The free EDICT and KANJIDIC dictionaries are required for use.  They are not
  included with this distribution because they are updated on a near-daily 
  basis.  There should be direct download links on my website (see the NOTICES
  section near the end of this file); alternatively, they can be downloaded 
  here:

    ftp://ftp.monash.edu.au/pub/nihongo/00INDEX.html#dic_fil

  The latest EDICT is in the file "edict.gz" (or "edict.zip", which includes
  some extra documentation for developers and contributors).  KANJIDIC is a
  couple of screens farther down the above web page, in the file "kanjidic.gz"
  (or "kanjidic.zip").  You may also want the 'kanjidoc' file (available in a
  couple of different formats), as it contains useful information about the 
  various fields shown for each kanji.
  ------------------------------------------------------------------------------

  Extract all files to a suitable directory.

  Unpack the EDICT and KANJIDIC files into the same directory (you can place
  them in a different directory if you like, but you will need to specify the
  "dicdir" option in your control file; see below).

  Run the following commands from the directory where you extracted the program
  files:

    xjdxgen.exe edict
    xjdxgen.exe kanjidic

  This will generate the required index files "edict.xjdx" and "kanjidic.xjdx".
  (If the files "edict" and "kanjidic" are in a different directory, specify the
  full path to them in the above commands.)

  XJDIC makes use of an optional control file called ".xjdicrc".  This can be
  located in the program directory, in your HOME directory, or under the
  directory indicated by the environment variable XJDIC.  This file allows you
  to configure the program in various ways.  For running under OS/2, a sample 
  ".xjdicrc" might contain:

      omode s
      exactmatch

  This causes XJDIC to display Japanese output in Shift-JIS format (which is
  what Japanese OS/2 normally uses), and to perform searches using complete
  word matches only.

  If you keep your dictionary files (EDICT and KANJIDIC) in a separate directory
  (e.g. e:\var\dicts) you should add:

      dicdir e:/var/dicts

  (or whatever directory you used) so that XJDIC can find the dictionaries.

  The text file "xjdic24.inf" contains a complete description of the control
  file format.  A sample file is also provided as ".xjdicrc.skel".  


RUNNING THE PROGRAM

  Read the following carefully, because there are several things you must do in
  order to use XJDIC effectively!

  * First, you should be running under an OS/2 environment capable of displaying 
    Japanese characters (hiragana, katakana, and kanji) from a command prompt.  
    If you don't have a Japanese version of OS/2, you will need the 'KShell' 
    utility by KO Myung-Hun.

    ----------------------------------------------------------------------------
    KShell allows the display of double-byte characters in an emulated console 
    (VIO) environment without requiring a DBCS version of OS/2.  It is available
    on Hobbes:
      http://hobbes.nmsu.edu/cgi-bin/h-search?key=kshell&pushbutton=Search

    The first time you run KShell, use the window menu next to the titlebar to 
    set both the desired font (see below) and the correct codepage (which is 943
    or its alias, 932).  You may need to close and restart KShell for these 
    changes to take effect properly (although this does not seem to be an issue 
    with the latest release).
    ----------------------------------------------------------------------------

    Without support for Japanese text display, the program will still work; but 
    all of the Japanese text will come out looking like gibberish.  (In theory 
    you could copy and paste the output into a graphical editor capable of 
    Japanese display in order to read it, but this is hardly an ideal solution.)

  * You will need a Japanese-capable monospaced font to use with KShell.  
    (Unfortunately, KShell does not work well with the monospaced Unicode font
    that comes with OS/2, 'Monotype Sans Duospace'.)
 
    Every 4.5x version of OS/2 has two Japanese fonts on the install CD under 
    \OS2IMAGE\FI\FONT: DFHSM-W3.ZIP contains 'Heisei Mincho' (serif) and 
    DFHSG-W5.ZIP contains 'Heisei Gothic' (sans-serif).  (As both these fonts
    are poorly hinted and rather ugly, you may want to find a better font
    somewhere.  "MS Gothic" (MSGOTHIC.TTF) is pretty good, if you have access to
    a Windows system.)
 
  * You are recommended to have a TERM environment variable defined.  (If you 
    don't, XJDIC will print repeated warning messages, although the program 
    still seems to work OK.)  This requires TERMCAP or the equivalent to be 
    installed and configured.  (If you have the EMX runtime, you can refer to 
    its documentation for information on how to set up TERMCAP.)  Any valid TERM
    setting seems to be acceptable, such as "ansi" or "mono".  If you don't have
    one set, you can run XJDIC from a batch file like the following:

    @echo off
    setlocal
    set term=mono
    xjdic_sa.exe %1 %2 %3 %4 %5 %6 %7 %8 %9
    endlocal

| * Since OS/2 uses codepage 932/943 to display Japanese text, XJDIC must be 
|   run in Shift-JIS output mode.  The latest OS/2 build defaults to this 
    mode.  (It can also be specified explicitly either by adding "omode s" to 
    your ".xjdicrc" control file, or else by using the parameter "-j s" on the 
    command line.)

  * XJDIC supports a number of command-line options; refer to "xjdic24.inf" or
    the man page for details.  Many of these options can also be set from the
    control file (see above).


  There are two different versions of the program: a client/server version, and
  a standalone version that works like any other application.  Most users will
  probably prefer to use the standalone version, "xjdic_sa.exe".  For 
  information about using the client/server version, see the section titled
  'CLIENT/SERVER OPERATION', below.


USING THE PROGRAM

  See "xjdic24.inf" for details (note that this is a plain-text file, in spite
  of the extension).  A very brief summary of operation is given below.

  To search for an English word, type the word at the prompt and press Enter.

  To search for a Japanese word in hiragana, katakana, or kanji, also type it
  at the prompt and press Enter (obviously, this requires support for Japanese
  character input).  Alternatively, you can copy and paste it into the prompt
  from another program, like Mozilla.

  To search for a romanized Japanese (romaji) word, type a '@' character (for
  hiragana) or a '#' character (for katakana), then type the word using the
  standard IME (or 'wapuro') style, and press 'Enter'.  The word will be 
  converted to the corresponding Japanese characters as you type. 

  Search results will be returned, line by line, in the format:

    match_length: KANJI (kana) English terms (separated by semicolons)

  Besides word lookups, you can also do lookups on specific kanji or their
  equivalent English meanings.  Press '\' to run enter kanji-lookup mode.
  There are several different input forms you can use; see the program help or
  "xjdic24.inf" for details.

  Pressing '?' will give you the program help.

  Press Ctrl-D to exit.

  There are many other features available in XJDIC.  Again, refer to the
  documentation for details.


CLIENT/SERVER OPERATION

  The client/server version consists of the executables "xjdic_cl.exe" and
  "xjdserver.exe".  This allows you to keep the dictionary files on a separate
  server, and run just the client locally.

  To use the client/server version, make sure that "xjdserver.exe", the EDICT
  and KANJIDIC dictionaries, and the index files "edict.xjdx" "kanjidic.xjdx"
  are all located on the server.  (You are also advised to have "xjdxgen.exe"
  installed on the server as well, in case you install updated dictionaries.)

  "xjdic_cl.exe", "gnu_licence", "kanjstroke", "radicals.tm", "radkfile",
  "romkana.cnv" and "vconj" must all be installed on the local system from
  which the client will be run.

  Both the client and server can make use of ".xjdicrc" control files.  The
  descriptions in "xjdic24.inf" indicate the context in which each keyword can
  be used.

  By default, the server listens on UDP port 47512.  This can be changed from
  the command line or the control file.

  By default, the client tries to connect to the server "localhost" (the local
  loopback address).  This, too, can be changed from the command line or the
  control file.


BUGS AND LIMITATIONS

  1.  The "suspend" (Ctrl-Z) function has been disabled for the OS/2 build,
      as neither EMX nor kLIBC appears to support the SIGTSTP signal used.

  2.  Since XJDIC was written for Unix, the original source code tended to
      assume that end-of-line characters were 0x0a rather than 0x0d0a.  I fixed
      this in the case of input at the search prompt, but I did notice the code
      doing some checks for 0x0a in other places (which I left unchanged
      whenever I wasn't 100% sure what it was doing).  If you ever come across a
      circumstance where the Enter key doesn't work as expected, that's probably
      why (and please let me know if you do).

| 3.  Due to limitations in the fork() system call, the server program will not
      automatically run as a background process.  To run it as a daemon, use the
      OS/2 "detach" command instead.  

| 4.  A build of the "xjdrad" utility (refer to "xjdic24.inf" for a description) 
      was included just for completeness.  However, since it outputs entirely in 
      EUC-JP (Japanese Unix encoding), it really isn't much use under OS/2.  For
      this reason, I have included a simple text file, "xjdrad.txt", which 
      contains the output from "xjdrad" converted into Shift-JIS (and should 
      therefore be readable under OS/2 codepage 932).

| 5.  Some versions of EDICT from 2008 did not work with this program, for
|     whatever reason.  This seems to have been rectified in more recent
|     releases.


BUILDING FROM SOURCE

  To build XJDIC for OS/2, you need either GCC 3.3.5 (available from NetLabs), 
  or else EMX+GCC version 0.9d-fix4 (on Hobbes).  You also need the GNU patch 
  and make utilities, as well as tar and gzip for extracting the source tarball.

  1. Get the XJDIC source code (currently xjdic24.tgz) from the product website:
     http://www.csse.monash.edu.au/~jwb/xjdic/

     Extract this file into a directory of your choice.

  2. Download my OS/2 patches and extract them into the same directory: 
|    http://www.socis.ca/~ataylo00/programming/ports/xjdic/patches_os2.zip

     (Patches were created using 'diff -b [orgfile] [newfile] > [file].diff'.)

  3. Assuming that GNU patch is installed as gnupatch.exe, apply the source code
     patches as follows:
  
     gnupatch -b -p0 Makefile Makefile.diff
     gnupatch -b -p0 xjdfrontend.c xjdfrontend.c.diff
     gnupatch -b -p0 xjdclient.c xjdclient.c.diff

  4. Run 'make' to build all targets.



PORT HISTORY

| 2009-06-30 (release 5)
|  - Fixed bug requiring the user to press Enter before typing or pasting
|    text in kanji lookup mode (only applies to xjdic_cl and xjdic_sa).
|  - Various corrections to out-of-date information in this README file.

  2008-08-15 (release 4)
   - Fixed the getcharxx() implementation (again) to stop the program from 
     hanging when a control key is pressed.

  2008-03-24 (release 3)
   - OS/2 front-end now defaults to Shift-JIS output mode.
   - Added xjdrad.exe and xjdrad.txt to the distribution package.
   - Fixed some careless coding in OS/2 getcharxx() implementation which caused
     slightly inconsistent input behaviour under some circumstances.
   - Disabled the daemon mode in xjdserver, and removed the -k switch from the 
     help text.
   - Removed the Ctrl-Z command from the online help screen.
   - Changed compiler to GCC 3.3.5 and kLIBC.

  2006-06-08 (release 2)
   - Fixed broken kanji lookups when running under KShell.

  2006-04-26 (release 1)
   - First release.


NOTICES

  XJDIC is (C) 2003 J.W. Breen.  The product website is
  http://www.csse.monash.edu.au/~jwb/xjdic/

  The original XJDIC source code is available at the website above.  My changes
  to the source are available (as diffs) here:
| http://www.socis.ca/~ataylo00/programming/ports/#xjdic

  This OS/2 port was built by Alex Taylor.  Minor additions were made to the
  source files "xjdfrontend.c", "xjdclient.c", and "xjdserver.c", as well as to
  "Makefile".  These modifications should be available in the same place where 
  you obtained this distribution.  Please contact me for questions or bug 
  reports specific to this port:
| E-mail:  alex -at- altsan -dot- org
| WWW:     http://www.socis.ca/~ataylo00/


    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 1, or (at your option)
    any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.


  EDICT and KANJIDIC have their own licenses; refer to their respective
  distributions for details.

--
Alex Taylor
June 2009
