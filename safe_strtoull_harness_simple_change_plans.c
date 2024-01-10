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
    errno = 0;
    *out = 0;
    char *endptr;
    unsigned long long ull = strtoull(str, &endptr, 10);
    if ((errno == ERANGE) || (str == endptr)) {
        return false;
    }
    //errno becomes relevant for implementation again when strtoull is reimplemented 
    //and our harness allows for bigger values outside of ull max range
    //-> makes experiment sequence for tomorrow clear: 
    //0) undo memchr() removal (add back in later if i run into infinite loop probelms with a property)
    //1) reimplement strtoull (as our method is pointless otherwise) 
    //(test my strtoull implementation first with testcases i made, then with esbmc to report results)
    //2) expand nondet range in harness (so errno becomes relevant)
    //3) reimplement errno
    //also expand harness to hit on xisspace and memchr issues at some point
    //and add sybolic assertions about where output values should land

    if (xisspace(*endptr) || (*endptr == '\0' && endptr != str)) {
        if ((long long) ull < 0) {
            if (memchr(str, '-', endptr - str) != NULL) {
                return false;
            }
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
    //try allocating this dynamically with malloc instead of statically with an array, to see whether more memsafety errors are created this way
    //remember to free the allocated memory again before the end of the harness!:
    //->
    //char *str = (char *)malloc(sizeof(char) * sizeStr);
    //for (unsigned int i = 0; i < sizeStr-1; ++i){*(str + i) = __VERIFIER_nondet_char();}
    //*(str + (sizeStr-1)) = '\0';  
    //and at the end of the harness: free(str);



    uint64_t strVal = __VERIFIER_nondet_ulonglong();
    if(strVal >= 50 || strVal <= 3) {abort();}

//Main Verification Harness:
    for(unsigned int i = 0; i < sizeStr-1; i++) {
        char temp = __VERIFIER_nondet_char();
        if(temp == '-'){abort();}
		str[i] = temp; 
        //how does ERANGE respond when we have a string like "-111"
        //-> ERANGE is only for MAX value. For "-111" we would still get errno != ERANGE
        //-> if(temp == '-'){abort();} not needed, maybe add in a later case
	}
	str[sizeStr-1] = '\0';

    bool safe = safe_strtoull(str,&strVal);

//Encode Postcondition (Assert):
    //should make assertion about strVal here in a later experiment
    if(safe){
        //__ESBMC_assert(strVal == ..., "Incorrect result for valid input");
        //"-1" -> __ESBMC_assert(!safe, "Conversion succeeded for invalid input"); 
        //in cases like ((errno == ERANGE) || (str == endptr)) OR 
        //!((xisspace(*endptr) || (*endptr == '\0' && endptr != str))) OR 
        //(memchr(str, '-', endptr - str) != NULL)  
        
        //maybe try an experiment with a harness that has the char '-' followed by nondet_char, to see if safe is reachable (which it shouldnt be with that harness), 
        //and with what counterexample states!!! i know it is, from what in noticed before!

        //generally i could make a harness that eliminates all the positive cases thaat should lead to safe, with abort() conditions, then see if/how safe is still reachable anyway!
        //then i could do the inverse with !safe
        return 1;
    } else{
	    //"123" -> __ESBMC_assert(safe, "Conversion failed for valid input");
        return 0;
    }
  
}
