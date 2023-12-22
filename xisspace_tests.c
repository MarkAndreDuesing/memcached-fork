#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define xisspace(c) isspace((unsigned char)c)

extern void appendString(char **str, char c);

int main(){

	char *myString1 = NULL;	
	char *myString2 = NULL;	

	for (int k = 0; k < 128 /*int k = -128; k <= 256*/ /*int k = 0; k < 256*/ /*int k = -128; k < 128*/; k++) {
	//use 0-127 for full correct range output
	//signed char ch = k;
	char ch = k;
//    	if(xisspace(ch)){printf("%c,' '", ch);}
	//printf("'%c',", ch);
	if(xisspace(ch)){appendString(&myString1, ch);} else {appendString(&myString2, ch);}
//	printf("digit:'%d', char:'%c'", ch, ch);
	}


    //printf("Resulting String: %s", myString1);
    for (int k = 0; k < strlen(myString1); k++) {printf(" digit:'%d', char:'%c'\n", myString1[k], myString1[k]);}
    
//    printf("\nResulting String: %s", myString2);
//    for (int k = 0; k < strlen(myString2); k++) {printf("digit:'%d', char:'%c'\n", myString2[k], myString2[k]);}
    
    free(myString1);
    free(myString2);
    
    if(xisspace('\0')){printf("\nassert true");}else{printf("\nassert false");}
    printf("\ndigit:'%d', char:'%c'\n", '\0', '\0');
    //assertion is false, because /0 isnt a space, its the lack of a space, its just the empty char!!!

    if(xisspace('\n')){printf("\nassert true");}else{printf("\nassert false");}
    printf("\ndigit:'%d', char:'%c'\n", '\0', '\0');
    //assertion is true for /n, despite also being represented by 
    //digit:'0', char:'' so i have to watch out for escape characters, that arent listed as part of the char range i guess
    //on cpp.sh it comes out to digit:10! check again and compare (is this a C vs C++ thing?)
    //Ask Thomas!
    

return 0;
}
//char(9) is the tab
//char(10) is the line feed (\n is also interpreted as this)
//char(11) is the vertical tab
//char(12) is the form feed
//char(13) is the carriage return
//char(32) is the space
//out of those the only one were realisticallly going to encounter is the char(32)


//char(0) a.k.a. \0 is not included among these, as its the empty char, not a space!

//gcc test.c -o test.exe
//./test.exe





void appendString(char **str, char c) {
    size_t currentLength = *str ? strlen(*str) : 0;

    // Allocate memory for the new character
    *str = realloc(*str, currentLength + 2);  // +2 to accommodate the new character and the null terminator

    // Check if reallocation was successful
    if (*str == NULL) {
        fprintf(stderr, "Memory allocation failed\n");
        exit(EXIT_FAILURE);
    }

    // Add the character to the end of the string
    (*str)[currentLength] = c;
    (*str)[currentLength + 1] = '\0';  // Null-terminate the string
}



