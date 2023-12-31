#include <stdio.h>
#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdint.h>//for uint64_t
#include <stdbool.h>//for bool

#define xisspace(c) isspace((unsigned char)c)

//needed implicit declarations
extern unsigned int __VERIFIER_nondet_uint();
extern uint64_t __VERIFIER_nondet_ulonglong();
extern char __VERIFIER_nondet_char(); 
extern unsigned long long int strtoull (const char *__restrict __nptr, char **__restrict __endptr, int __base);

bool safe_strtoull(const char *str, uint64_t *out) {
    assert(out != NULL);
    //errno = 0;
    *out = 0;
    //char *endptr;

    //various possible fixed values for endptr:
    //char *endptr = 'a';
    //char *endptr = 64;
    //char *endptr = &str[0];// equivalent to:
    char *endptr = str;
    //char test = 'a'; char *endptr = &test;//test to see if this works correctly
    //char *endptr = strchr(str, '\0');//test to see if this works correctly
    //char *endptr = str + strlen(str);//test to see if this works correctly
    

    //unsigned long long ull = strtoull(str, &endptr, 10);
    unsigned long long ull = 1;
    //if ((errno == ERANGE) || (str == endptr)) {
    //    return false;
    //}

    if (xisspace(*endptr) || (*endptr == '\0' && endptr != str)) {
        //potential assertions for the value of endptr:
        //assert(*endptr == 'a');
        //assert(*endptr == '\0');
        //assert(endptr != str);
        //assert(xisspace(*endptr));
        if ((long long) ull < 0) {
            //if (memchr(str, '-', endptr - str) != NULL) {
            //    return false;
            //}
        }
        *out = ull;
        return true;
    }
    return false;
}


int main(){

//Encode Precondition (Arrange):
	unsigned int sizeStr = __VERIFIER_nondet_uint();
	if(sizeStr >= 15 || sizeStr <= 3) {abort();}
	char str[sizeStr];

    uint64_t strVal = __VERIFIER_nondet_ulonglong();
    if(strVal >= 50 || strVal <= 3) {abort();}

//Main Verification Harness:
    for(unsigned int i = 0; i < sizeStr-1; i++) {
		str[i] = __VERIFIER_nondet_char(); 
	}
	str[sizeStr-1] = '\0';

    bool safe = safe_strtoull(str,&strVal);

//Encode Postcondition (Assert):
    if(safe){
        return 1;
    } else{
	    return 0;
    }
}