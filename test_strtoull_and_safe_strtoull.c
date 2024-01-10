//Implementations:

//strtoull (only need to do for base 10):


//Implementation based on \url{https://github.com/torvalds/linux/blob/master/arch/powerpc/boot/stdlib.c#L13}:
#include <stdio.h>
#include <stdarg.h>
#include <assert.h>  //for assertions
#include <ctype.h>   //for isspace()
//#include <errno.h>   //for errno
#include <string.h>  //for memchr
//#include <stdlib.h>  //for strtoull
#include <stdint.h>  //for uint64_t
#include <stdbool.h> //for bool
#include <limits.h>//for ULLONG_MAX


#define xisspace(c) isspace((unsigned char)c)
#define ERANGE 34

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
    errno = 0;
    *out = 0;
    char *endptr;
    unsigned long long ull = strtoull(str, &endptr, 10);
    if ((errno == ERANGE) || (str == endptr)) {
        return false;
    }

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



//Main Verification Harness:



    char str[] = "-1";
    uint64_t strVal = 10;

    printf("\"%s\"\n",str);

  printf(" str     :%p, * str      :'%c'\n", str, * str); 
  printf(" str+1   :%p, *( str+1)  :'%c'\n", str+1, *( str+1)); 
  printf(" str+2   :%p, *( str+2)  :'%c'\n", str+2, *( str+2)); 
  printf(" str+3   :%p, *( str+3)  :'%c'\n", str+3, *( str+3)); 
  printf(" str+4   :%p, *( str+4)  :'%c'\n", str+4, *( str+4)); 
  printf(" str+5   :%p, *( str+5)  :'%c'\n", str+5, *( str+5));
  printf(" str+6   :%p, *( str+6)  :'%c'\n", str+6, *( str+6)); 
  printf(" str+7   :%p, *( str+7)  :'%c'\n", str+7, *( str+7));
  printf(" str+8   :%p, *( str+8)  :'%c'\n", str+8, *( str+8));
  printf("& str+1  :%p, *(& str+1) :'%c'\n",& str+1, *(& str+1)); 

    //printf("\n%p",ptr);
    char *pEnd; unsigned long long temp;


  temp = strtoull (str, &pEnd, 10);
  printf("value as ull: %llu, value as ll: %lld, and pEnd adresse: %p, with input: \"%s\" \n",temp,temp,pEnd,str);

    errno = 0;
    unsigned long long ull_true = strtoull(str, &pEnd, 10);
    if (((long long) ull_true < 0)&&(memchr(str, '-', pEnd - str) != NULL)) {printf("True -> return false!!!!\n");} else {printf("False -> return ull!!!!\n");}
    printf("\n%d",errno);
    printf ("\nThe decimal equivalents are: llu: %llu\n", (long long) ull_true);
    printf ("\nThe decimal equivalents are: lld: %lld\n\n", (long long) ull_true);





    errno=0;
    bool safe = safe_strtoull(str,&strVal);
    printf("\nerrno: %d",errno);
//Encode Postcondition (Assert):
    if(safe){
        printf("\nmethod returned true and ull value:%llu\n",strVal);
        return 1;
    } else{
        printf("\nmethod returned false and ull value:%llu\n",strVal);
        printf("\n(long long) strVal: llu=%llu,:lld=%lld\n",(long long) strVal,(long long) strVal);
        
	    /*
        assert(
        (errno == ERANGE) || 
        (str == pEnd) || 
        (
            (errno != ERANGE) && (str != pEnd) && 
                (
                    ((!xisspace(*pEnd)) && (*pEnd != '\0'))
                    || 
                    (
                    ((long long) strVal < 0) && (memchr(str, '-', pEnd - str) != NULL) && 
                        (
                            xisspace(*pEnd) 
                            || 
                            (*pEnd == '\0')
                        )
                    )
                )
        )
        );
        */

        assert(
        false || 
        false || 
        (
            true && true && 
                (
                    (true && false)
                    || 
                    (
                    ((long long) strVal < 0) && (memchr(str, '-', pEnd - str) != NULL) && 
                        (
                            xisspace(*pEnd) 
                            || 
                            (*pEnd == '\0')
                        )
                    )
                )
        )
        );

        return 0;
    }
}
