#include <stdio.h>
#include <stdarg.h>
#include <assert.h>  //for assertions
#include <ctype.h>   //for isspace()
#include <errno.h>   //for errno
#include <string.h>  //for memchr
#include <stdlib.h>  //for strtoull
#include <stdint.h>  //for uint64_t
#include <stdbool.h> //for bool

#define xisspace(c) isspace((unsigned char)c)

//needed implicit declarations:
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

/*
    unsigned long long ull2 = 9223372036854775808;    
    printf("\n%llu",ull2);
    uint64_t ull3 = 9223372036854775808;
    printf("\n%llu",ull3);


    signed int ull3 = 4294967293;    
    printf("\n%llu",ull3);
    unsigned int ull4 = 4294967293;
    printf("\n%llu",ull4);
*/

    unsigned long long ulli = strtoull("-1", NULL, 10);//18446744073709551615
    printf ("\nThe decimal equivalents are: llu: %llu\n", (long long) ulli);
    printf ("\nThe decimal equivalents are: lld: %lld\n\n", (long long) ulli);

//(long long) ull < 0
//-> value has to be greater than 9,223,372,036,854,775,807

//If theres a minus in the string and the converted to signed long long value is less than 0 -> false

//what if you have "9223372036854775808-123"

  printf("input: \"18446744073709551614\"; value as llu: %llu; value as lld: %lld \n",strtoull ("18446744073709551614", NULL, 10), strtoull ("18446744073709551614", NULL, 10));
  //ull value = 18446744073709551614
  printf("input: \"18446744073709551615\"; value as llu: %llu; value as lld: %lld \n",strtoull ("18446744073709551615", NULL, 10), strtoull ("18446744073709551615", NULL, 10));
  //ull value = 18446744073709551615
  printf("input: \"18446744073709551616\"; value as llu: %llu; value as lld: %lld \n",strtoull ("18446744073709551616", NULL, 10), strtoull ("18446744073709551616", NULL, 10));
  //ull value = 18446744073709551615 -> errno == ERANGE
  
  //As can be seen here underflows do not set off errno == ERANGE, unless the values are so negative that they cycle back into being overflows:
  printf("input: \"-1\"; value as llu: %llu; value as lld: %lld \n",strtoull ("-1", NULL, 10), strtoull ("-1", NULL, 10));
  //ull value = 18446744073709551615
  printf("input: \"-2\"; value as llu: %llu; value as lld: %lld \n",strtoull ("-2", NULL, 10), strtoull ("-2", NULL, 10));
  //ull value = 18446744073709551614
  //...works in this interval
  printf("input: \"-9223372036854775808\"; value as llu: %llu; value as lld: %lld \n",strtoull ("-9223372036854775808", NULL, 10), strtoull ("-9223372036854775808", NULL, 10));
  //ull value = 9223372036854775808, signed long long value = -9223372036854775808
  printf("input: \"-9223372036854775809\"; value as llu: %llu; value as lld: %lld \n",strtoull ("-9223372036854775809", NULL, 10), strtoull ("-9223372036854775809", NULL, 10));
  //ull value = 9223372036854775807, signed long long value = 9223372036854775807
  //            926882201685326643
  //-> problem for: if ((long long) ull < 0) check, which we want to return true, but doesnt in this range
  //...doesnt work in this interval (as underflow for signed int)
  printf("input: \"-18446744073709551615\"; value as llu: %llu; value as lld: %lld \n",strtoull ("-18446744073709551615", NULL, 10), strtoull ("-18446744073709551615", NULL, 10));
  //ull value = 1, signed long long value = 1
  printf("input: \"-18446744073709551616\"; value as llu: %llu; value as lld: %lld \n",strtoull ("-18446744073709551616", NULL, 10), strtoull ("-18446744073709551616", NULL, 10));
  //ull value = 18446744073709551615 -> errno == ERANGE
  //works with more negative values again
  
    char *endptr;
    char str_true[] = "-9912337881327533328";//-1 to -9223372036854775808 works; -18446744073709551616 to -infinity works; 
    //starting at -9223372036854775809 signed long long int also has an underflows, leading to the issue, that (long long) ull_true < 0 is no longer true, despite the negative input value
    //char str_true[] = "9999999999999999999999999999999999999999999999999999999999";
    errno = 0;
    //unsigned long long ull_true = strtoull(str_true, &endptr, 10);
    unsigned long long ull_true = strtoull(str_true, &endptr, 10);
    if (((long long) ull_true < 0)&&(memchr(str_true, '-', endptr - str_true) != NULL)) {printf("True -> return false!!!!\n");} else {printf("False -> return ull!!!!\n");}
    printf("\n%d",errno);
    printf ("\nThe decimal equivalents are: llu: %llu\n", (long long) ull_true);
    printf ("\nThe decimal equivalents are: lld: %lld\n\n", (long long) ull_true);



//Main Verification Harness:



    char str[] = "\t-1"; //something like -10000000000000000000 clearly shouldnt work like this!!!
    //-13062422948784164494
    //dont forget the "+123" case
    //whit safe_strtoull "123 B" is true, but "123B" is false
    uint64_t strVal = 10;

    printf("\"%s\"\n",str);

    char *ptr;
    unsigned long long ull = strtoull(str, &ptr, 10);


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

    printf("\n%p",ptr);

    errno=0;
    bool safe = safe_strtoull(str,&strVal);
    printf("\nerrno: %d",errno);
//Encode Postcondition (Assert):
    if(safe){
        printf("\nmethod returned true and ull value:%llu\n",strVal);
        return 1;
    } else{
        printf("\nmethod returned false and ull value:%llu\n",strVal);
	    return 0;
    }
}


int main2(){//to test if *(endptr+strlen(str)) works as expected, which it doesnt if we have a \0 inside the string -> main3:
    char str[] = "123 B";
    char *endptr = str;
    char *endptr2 = str+strlen(str)-1;
    char *endptr3 = str+strlen(str);
    printf("1:'%c'\n",*endptr);
    printf("2:'%ld'\n",strlen(str));
    printf("3:'%s'\n",endptr);
    printf("4:'%c'\n",*(endptr+strlen(str)-1));
    printf("5:'%c'\n",*(endptr+strlen(str)));
    
    printf("6:'%c'\n",*endptr2);
    printf("7:'%c'\n",*endptr3);
    if(isspace(*endptr)){printf("isspace(endptr)==true");}else{printf("isspace(endptr)==false");}
    return 0;
}


int main3(){
    char str[] = "\0 1\0 23\0 B";
    char *endptr = str;
    char *endptr2 = str+strlen(str)-1;
    char *endptr3 = strchr(str, '\0');
    char *endptr4 = str+strlen(str);
    printf("1:'%c'\n",*endptr);
    printf("2:'%ld'\n",strlen(str));
    printf("3:'%s'\n",endptr);
    printf("4:'%c'\n",*(endptr+strlen(str)-1));
    printf("5:'%c'\n",*(endptr+strlen(str)));
    
    printf("6:'%c'\n",*endptr2);
    printf("7:'%c'\n",*endptr3);
    if(endptr3==endptr4){printf("endptr3==endptr4\n");}
    if(isspace(*endptr)){printf("isspace(endptr)==true");}else{printf("isspace(endptr)==false");}
    if(isspace(*endptr3)){printf("isspace(endptr)==true");}else{printf("isspace(endptr)==false");}
    
    printf("\n9:'%c%c%c%c%c'\n",0,-128,0,64,0);
    if(endptr4 == str){printf("endptr == str\n");}
    
}
