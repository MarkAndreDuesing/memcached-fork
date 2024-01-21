#include <stdio.h>
#include <assert.h>
#include <ctype.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdint.h>//for uint64_t
#include <stdbool.h>//for bool
#include <limits.h>//for ULLONG_MAX

#define xisspace(c) isspace((unsigned char)c)
#define ERANGE 34

//... [__VERIFIER_nondet_X declarations]

int errno = 0;

unsigned long long int strtoull(const char *ptr, char **end, int base){
    char *str_start_ptr = ptr;
	unsigned long long ret = 0;
    bool negative_sign = false;
    bool ull_overflow = false;
    bool values_read = false; 
    //so **end still shows to the start of the string, even though we iterated over ptr repeatedly,
    //for cases like "\n\n\n+" or "--"
    //But cases like "0000" should still point to the end of the string
    bool lead_space_break = false; //set to true as soon as a non-whitespace character is read

	while (*ptr) {// false when *ptr== '\0'
		int digit;
        if (((*ptr == ' ') || ((*ptr - 9) < 5)) && !lead_space_break){ //cases for char 9-13 and 32
            digit = 0;
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
        } else {
			break;
            //important to break off while loop here, 
            //so we dont increase ret by another *=10 when we have a char like 'A'
            //and so my ptr is pointing to 'A'
        }

        //Checking overflows and implementing errno:
        //ULLONG_MAX = 18446744073709551615
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
            }
        } else {
            ret = ULLONG_MAX;
            ull_overflow = true;
        }
		
		ptr++;
	}

    if(negative_sign){
        if(ull_overflow){
            ret=ULLONG_MAX; //account for cases like  "-18446744073709551616" and beyond where the result should be ull value = 18446744073709551615
        } else {
            ret *= -1;      //account for cases up to "-18446744073709551615"            where the result should be ull value = 1
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
    errno = 0;
    *out = 0;
    char *endptr;
    unsigned long long ull = strtoull(str, &endptr, 10);
    if ((errno == ERANGE) || (str == endptr)) {
        return false;
    }
    if (isspace(*endptr) || (*endptr == '\0' /*&& endptr != str*/)) {
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
    bool split_path = __VERIFIER_nondet_bool();
    unsigned int sizeStr = __VERIFIER_nondet_uint();
    if(split_path){//split_path==true for cases without '-', where sizeStr can be >= 22 as the very low value range case isnt an issue
        if(sizeStr >= 25|| sizeStr <= 0) {abort();}
    } else {
        if(sizeStr >= 21|| sizeStr <= 0) {abort();}//for cases allowing '-'
        //go down from 25 to 21 to eliminate cases of -9.223.372.036.854.775.809 + /0 etc.
    }
    char *str = (char *)malloc(sizeof(char) * sizeStr);
    uint64_t strVal = __VERIFIER_nondet_ulonglong();

//Main Verification Harness:
    for (unsigned int i = 0; i < sizeStr-1; ++i){
        char temp = __VERIFIER_nondet_char();
        if(temp == '\0'){abort();}   
        if(split_path && temp == '-'){abort();}
        *(str + i) = temp; 
    }
    *(str + (sizeStr-1)) = '\0';  
    bool safe = safe_strtoull(str,&strVal);

//Encode Postcondition (Assert):
    if (strVal!=0){
    // ... [various assertions]
    }
    if(safe){    
    // ... [various assertions]
    } else {
    // ... [various assertions]
    }
    free(str);
    return 0;
}