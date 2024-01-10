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
    //check if str can be NULL at any point in memcached!

    //errno = 0;
    *out = 0;

    //ask Thomas:!
    //int wert;
    //if(wert <10){}//default werte bei C?
    char *endptr;//=&str[0];//=64; //what is the value: endptr = INVALID6 or endptr = INVALID7 ?
    //and what is value: endptr = invalid-object ?
    //when do we use:
    //type *name;
    //and when:
    //type* name;
    
    //if *endptr automatically initialised with value &str[0] i get the assert(xisspace(*endptr))=false 
    //after doing strtoull(str, &endptr, 10);, which is logical if strtoull leaves the value unchanged
    //i dont know if ESBMC does leave undefined functions unchanged though
	int length1 = strlen(str);
    //length1 = 5;//why wont this set correctly automatically?
	//int length2 = *(&str+1)-str;
	
    //printf("value:%c\n",*(str+length2-1));
    //printf("value:%c\n",*(endptr+length2-1));
    //also  double check if the standard strtoull actually sets &endptr to p+length2-1, or sets it to p+length2 !?
    //im pretty sure its the directly included \0, so p+length2-1. It points to the space that caused the reading to end


    //unsigned long long ull = strtoull(str, &endptr, 10);
    //str and base unchanged
    endptr=(str+length1-1);//endpointer shifted to first line breal, in this case directly at the end of the string
    //this assumes the case where the whole string is read correctly as int ending in \0
    
    unsigned long long ull = 1111;//assuming out string is something like "1111"
    //ull = 1111;

    //if ((errno == ERANGE) || (str == endptr)) {
    //    return false;
    //}
    assert(true);
    //assert(false);
    //assert(xisspace(*endptr));//false
    assert(*endptr == '\0');//false, true if endptr=(str+length2-1) or a space occurred before the end of the string
    assert(endptr != str);//true, unless *endptr=&str[0]
    //these 2 in combination assure that endptr points to a \0, either at the end or in the middle of the string, 
    //and that endptr isnt still pointing to the start of the str, which would mean that either str is just spaces or a digit couldnt be read somehow.
    //look at all the cases that endptr == str can happen with

    if (xisspace(*endptr) || (*endptr == '\0' && endptr != str)) {
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
	unsigned int sizeStr = 5;
	char str[sizeStr];

    //ask Thomas: !
    //why does ESBMC sometimes retrun much longer strings than needed or specified, z.b. hier:
//State 1 file safe_strtoull_harness_fixed_values.c line 80 column 2 function main thread 0
//----------------------------------------------------
  //str = { 0, 0, 0, 0, 0, 0, 0, 0 }
    //here it seems to think str length is 8, which affects the later error reports!


    uint64_t strVal = 10;

//Main Verification Harness:
    for(unsigned int i = 0; i < sizeStr-1; i++) {
		str[i] = '1'; 
	}
	str[sizeStr-1] = '\0';
    //ask Thomas: !
    printf("\"%s\"",str);//including lines like this produces unexpected behaviour, 
    //changing the returned counterexample, even though it shouldnt have an effect. ask why
    //Unexpected behaviour like:
  //Violated property:
  //file safe_strtoull_harness_fixed_values.c line 39 column 5 function safe_strtoull
  //assertion *endptr == '\0'
  //(*signed int)(*endptr) == 0
    //being returned, even though the assertion in line 38 is also false
    //or: 
  //endptr = INVALID6

    //int test_length;
    //test_length = sizeof(str);
    //ask Thomas: !
    //here im just probing why the size of the string is set larger than it should be, but it gives me a runtime error!:
//        endptr=(str+length1-1);//endpointer shifted to first line breal, in this case directly at the end of the string
//          ^~~~~~~~~~~~~~~~
//Converting
//terminate called after throwing an instance of 'array_type2t::dyn_sized_array_excp'
//Aborted (core dumped)


    //assert(strcmp(str,"1111\0")==0);
    //assert(strcmp(str,"1111")==0);
    //both true

    bool safe = safe_strtoull(str,&strVal);

//Encode Postcondition (Assert):
    if(safe){
        return 1;
    } else{
	    return 0;
    }

    //ask Thomas:!
    //im getting severely bogged down in the less directly relevant background parts and comprehension of C.
    //should i write all the small tests i did to show how C works down as well.
    //or should i just really simpliify my work, fix the methods optimally, 
    //use the esbmc wrapper, analyse the results and call it a day..
}
