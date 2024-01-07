#include <stdio.h>
#include <assert.h>
#include <ctype.h>
//#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdint.h>//for uint64_t
#include <stdbool.h>//for bool
#include <limits.h>//for ULLONG_MAX

#define xisspace(c) isspace((unsigned char)c)
#define ERANGE 34

//needed implicit declarations
extern unsigned int __VERIFIER_nondet_uint();
extern uint64_t __VERIFIER_nondet_ulonglong();
extern char __VERIFIER_nondet_char(); 

int errno = 0;

unsigned long long int strtoull(const char *ptr, char **end, int base)
{//typical strtoull implementation throws an error if ptr is set to NULL
//method breaks on /0 case as it should


//added challenge to implementation as I needed to avoid using other methods ESBMC doesnt support in creating this

    char *str_start_ptr = ptr;
    //see test_reference_error(). works as expected


	unsigned long long ret = 0;
    bool negative_sign = false;
    bool ull_overflow = false;

    bool values_read = false;
    //this is added to deal with cases where no numeric value is ever read, to make sure
    //**end still shows to the start of the string, even though we iterated over ptr repeatedly.
    //Cases like "\n\n\n+" or "--"
    //But cases like "0000" should still point to the end of the string

    bool lead_space_break = false;
    //set to true as soon as a non-whitespace character is read

	while (*ptr) {// false when *ptr== '\0'

		int digit;//important to reset digit here
        //test if i set int digit = 0; here if i can remove them in the cases


        
        
        if (((*ptr == ' ') || ((*ptr - 9) < 5)) && !lead_space_break){
            //cases for char 9-13 and 32
            digit = 0;//important to keep this case even if i remove the digit = 0; so i dont break here
        } else if ((*ptr == '+') && !lead_space_break){
            digit = 0;
            lead_space_break = true;
        } else if ((*ptr == '-') && !lead_space_break){
            digit = 0;
            negative_sign = true;
            lead_space_break = true;
        } else if (*ptr >= '0' && *ptr <= '9'){
			digit = *ptr - '0';
        //e.g. char(48)='0' to char(57)='9'
        //subtract 48 from those to get char(0) to char(9) 
        //-> convert into int digit -> digit can be int 0 to int 9
		lead_space_break = true;
        values_read = true;

        //see test method as to why repeated leading 0's arent an issue
        } else {
			break;
            //important to break of while loop here, 
            //so we dont increase ret by another *=10 when we have a char like 'A'
            //and so my ptr is pointing to 'A'
        }

//check what happens with leading 0's, 
//make cases for leading whitespaces (can go infinitely, but watch out for a string that is all whitespaces), 
//Check that if nothing could be read str=endptr is the case! In cases like "--" or "\n\n\n"
//but if i have "+00000" it should point to the last 0! also test safe_strtoull for this oddity!
//after first digit whitespaces break the sequence, so i need a case for after the first digit
//and a case for '-' and '+' only as the first char (after any potential leading whitespaces), otherwise they also break the sequence

        //Without errno implementation:
		//ret *= base;
		//ret += digit;//add to the end of the number
        //e.g. before ret was 4, then we have a new digit 5, then 4*10+5=45


        //Checking overflows and implementing errno:
        
        //ret<=1844674407370955161, where ULLONG_MAX = 18446744073709551615
        if (ret<ULLONG_MAX/10) {
		    ret *= base;
            ret += digit;
        } else if (ret==ULLONG_MAX/10){
            if(digit<=5){
                ret *= base;
                ret += digit;
            } else {
                ret = ULLONG_MAX;
                ull_overflow = true;
                //edit this case so that errno is set
            }
        } else {
            ret = ULLONG_MAX;
            ull_overflow = true;
        }
		

		ptr++;
	}

    if(negative_sign){//with this underflows are also processed the way strtoull() typically does
        if(ull_overflow){
            ret=ULLONG_MAX;
            //account for cases like "-18446744073709551616" and beyond where ull value = 18446744073709551615
        } else {
            ret *= -1;
            //account for cases up to "-18446744073709551615" where ull value = 1
        }
    }

	if (end){//check for case where pointer was set to NULL
        if(values_read){
		*end = (char *)ptr;
        } else {
        *end = (char *)str_start_ptr;
        }
    }
    if(ull_overflow){errno=34;}
	return ret;
}


bool safe_strtoull(const char *str, uint64_t *out) {
    assert(out != NULL);
    //errno = 0;
    *out = 0;
    char *endptr;

    //various possible fixed values for endptr:
    //char *endptr = 'a';
    //char *endptr = 64;
    //char test = 'a'; char *endptr = &test;
    //char *endptr = &str[0];// equivalent to:
    //char *endptr = str;
    //char *endptr = strchr(str, '\0');// equivalent to:
    //char *endptr = str + strlen(str);
    //assert(*endptr=='\0');
    //assert(endptr != str);

    unsigned long long ull = strtoull(str, &endptr, 10);
    //unsigned long long ull = 1;
    if ((errno == ERANGE) || (str == endptr)) {
        return false;
    }

    if (xisspace(*endptr) || (*endptr == '\0' && endptr != str)) {
        //potential assertions for the value of endptr:
        //assert(*endptr == 'a');
        //assert(*endptr == '\0');
        //assert(endptr != str);
        //assert(xisspace(*endptr));
        if ((long long) ull < 0) {
//            assert(0);//->TRUE, unreachable
            if (memchr(str, '-', endptr - str) != NULL) {
                return false;
            }
        }
        *out = ull;
//        assert(0);->FALSE_REACH, reachable
        return true;
    }
    //assert(0);//->TRUE, unreachable, if we exclude \0 from being added in our harness
    return false;
}


int main(){
//Encode Precondition (Arrange):
    unsigned int sizeStr = __VERIFIER_nondet_uint();
    if(sizeStr >= 15 || sizeStr <= 3) {abort();}
    char *str = (char *)malloc(sizeof(char) * sizeStr);
    uint64_t strVal = __VERIFIER_nondet_ulonglong();
    if(strVal >= 50 || strVal <= 3) {abort();}

//Main Verification Harness:
    for (unsigned int i = 0; i < sizeStr-1; ++i){
        char temp = __VERIFIER_nondet_char();
        if(temp == '\0'){abort();}
        if(temp == '-'){abort();}
        *(str + i) = temp; 
    }
    *(str + (sizeStr-1)) = '\0';  

    bool safe = safe_strtoull(str,&strVal);
        
//Encode Postcondition (Assert):
    if(safe){    
        free(str);
        return 1;
    } else{
        free(str);
        return 0;
    }
}