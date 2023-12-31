#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define xisspace(c) isspace((unsigned char)c)

extern void appendString(char **str, char c);

int main(){
	char *myString1 = NULL;	
	for (int k = 0; k < 128; k++) {
	    char ch = k;//signed or unsigned
	    if(xisspace(ch)){appendString(&myString1, ch);}
	}
    for (int k = 0; k < strlen(myString1); k++) {printf(" digit:'%d', char:'%c'\n", myString1[k], myString1[k]);}
    free(myString1); 
    return 0;
}
//so char 9-13 and 32 are recognised as whitespace by isspace:
//char(9) is the tab ('\t')
//char(10) is the line feed ('\n')
//char(11) is the vertical tab ('\v')
//char(12) is the form feed ('\f')
//char(13) is the carriage return ('\r')
//char(32) is the space (' ')
//out of those the only one were realisticallly going to encounter is the char(32)

//it is worth noting:
//char(0) a.k.a. '\0' is not included among these, as its the empty char, not a whitespace!

//https://en.cppreference.com/w/cpp/string/byte/isspace
//https://cplusplus.com/reference/cctype/isspace/
//https://www.cs.cmu.edu/~pattis/15-1XX/common/handouts/ascii.html

void appendString(char **str, char c) {
    //Credit: taken from Chat-GPT 
    size_t currentLength = *str ? strlen(*str) : 0;
    *str = realloc(*str, currentLength + 2);  //Allocate memory for the new character -> +2 to accommodate the new character and the null terminator
    (*str)[currentLength] = c;
    (*str)[currentLength + 1] = '\0';
}



