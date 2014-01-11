#include <stdio.h>
#include <string.h>
#include <stdlib.h>

FILE *fi,*fo,*fopen();
unsigned char instr[1000],*ptr;
int i;

main()
{
	fo = fopen("kanjstroke","w");
	if (fo == NULL)
	{
		printf("Unable to open output file: kanjstroke\n");
		exit(1);
	}
	fi = fopen("kanjidic","r");
	if (fi == NULL)
	{
		printf("Unable to open input file: kanjidic\n");
		exit(1);
	}
	while(!feof(fi))
	{
		fgets(instr,999,fi);
		if (feof(fi)) break;
		if (instr[0] < 127) continue;
		ptr = strstr(instr," S");
		i = atoi(ptr+2);
		fprintf(fo,"%c%c%c\n",instr[0],instr[1],i+'0');
	}
	fclose(fo);
}
