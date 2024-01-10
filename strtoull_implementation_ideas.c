//Implementations:

//strtoull (only need to do for base 10):


//Implementation based on \url{https://github.com/torvalds/linux/blob/master/arch/powerpc/boot/stdlib.c#L13}:
//#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <stdbool.h>

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


int leading_zeros(){
//here is an example of why leading zeros arent a problem with our implementation, 
//hence why we turn leading whitespaces into leading zeros
    unsigned long long numbers[] = {0,0,0,0,1,2,3,0,9};
    unsigned long long digit;
    unsigned long long ret = 0;
    size_t arraySize = sizeof(numbers) / sizeof(numbers[0]);
    
    for(size_t i = 0; i < arraySize; i++){
        digit=numbers[i];
        ret *= 10;
	    ret += digit;
    }
    printf("%llu",ret); //-> ret = 12309
    return 0;
}//doesnt account for overflow case yet, and negative sign case is left open (no error checks)!!!



int test_reference_error(){
    char tempstr[] = "abcd";
    char *endptr;
    inside_test(tempstr,endptr);
    return 0;
}

int inside_test(const char *ptr, char **end){
    char *str_start_ptr = ptr;
    printf("%s\n",ptr);
    printf("%c\n",*ptr);//-> 'a'
    printf("%c\n",*(str_start_ptr));//-> 'a'
    ptr++;
    printf("%c\n",*ptr);//-> 'b'
    printf("%c\n",*(str_start_ptr));//-> 'a'
    ptr++;
    printf("%c\n",*ptr);//-> 'c'
    printf("%c\n",*(str_start_ptr));//-> 'a'
    return 1;
}







int main()
{
  char *pEnd; unsigned long long int temp;
  
  printf("value: %llu, \nwith input: \"\" \n",strtoull ("", &pEnd, 10));//ull value = 0; pEnd points to ''
  //printf("value: %llu, \nwith input: NULL \n",strtoull (NULL, &pEnd, 10));//-> Segmentation fault (core dumped)
  printf("value: %llu, \nwith input: \" \" \n",strtoull (" ", &pEnd, 10));//ull value = 0; pEnd points to ' '
  printf("value: %llu, \nwith input: \"A\" \n",strtoull ("A", &pEnd, 10));//ull value = 0; pEnd points to 'A'
  printf("value: %llu, \nwith input: \"123A\" \n",strtoull ("123A", &pEnd, 10));//ull value = 0; pEnd points to ''

  
  char tempstr[] = "\t-1";//char tempstr[] = "  123  " // 0001-\n123  //0001++A //"5+ " //"5- "
  printf("tempstr     :%p, *tempstr      :'%c'\n",tempstr, *tempstr); 
  printf("tempstr+1   :%p, *(tempstr+1)  :'%c'\n",tempstr+1, *(tempstr+1)); 
  printf("tempstr+2   :%p, *(tempstr+2)  :'%c'\n",tempstr+2, *(tempstr+2)); 
  printf("tempstr+3   :%p, *(tempstr+3)  :'%c'\n",tempstr+3, *(tempstr+3)); 
  printf("tempstr+4   :%p, *(tempstr+4)  :'%c'\n",tempstr+4, *(tempstr+4)); 
  printf("tempstr+5   :%p, *(tempstr+5)  :'%c'\n",tempstr+5, *(tempstr+5));
  printf("tempstr+6   :%p, *(tempstr+6)  :'%c'\n",tempstr+6, *(tempstr+6)); 
  printf("tempstr+7   :%p, *(tempstr+7)  :'%c'\n",tempstr+7, *(tempstr+7));
  printf("&tempstr+1  :%p, *(&tempstr+1) :'%c'\n",&tempstr+1, *(&tempstr+1)); 
  
  temp = strtoull (tempstr, &pEnd, 10);
  printf("value: %llu, and pEnd adresse: %p, with input: \"%s\" \n",temp,pEnd,tempstr); //input "0001-\n123" -> pEnd pointed to '-', value = 1

  
  //Base cases:
  printf("value: %llu, with input: \"\" \n",strtoull ("", &pEnd, 10));//ull value = 0; pEnd points to ''
  //printf("value: %llu, \nwith input: NULL \n",strtoull (NULL, &pEnd, 10));//-> Segmentation fault (core dumped)
  printf("value: %llu, with input: \" \" \n",strtoull (" ", &pEnd, 10));//ull value = 0; pEnd points to ' '
  printf("value: %llu, with input: \"A\" \n",strtoull ("A", &pEnd, 10));//ull value = 0; pEnd points to 'A'
  
  printf("value: %llu, with input: \"123\" \n",strtoull ("123", &pEnd, 10)); //ull value = 123; pEnd points to '' null string after 3
  printf("value: %llu, with input: \" 123\" \n",strtoull (" 123", &pEnd, 10)); //ull value = 123; pEnd points to '' null string after 3
  printf("value: %llu, with input: \"123 \" \n",strtoull ("123 ", &pEnd, 10)); //ull value = 123; pEnd points to ' ' empty space after 3 (the first one, thats still within the string)

  //chech whitespace characters
  printf("value: %llu, with input: \"\\n123 \" \n",strtoull ("\n123", &pEnd, 10)); //ull value = 123; pEnd points to ' ' empty space after 3 (the first one, thats still within the string)
  printf("value: %llu, with input: \"\\t123 \" \n",strtoull ("\t123", &pEnd, 10)); //ull value = 123; pEnd points to ' ' empty space after 3 (the first one, thats still within the string)
  
  printf("value: %llu, with input: \"000123\" \n",strtoull ("000123", &pEnd, 10));//ull value = 123 (leading 0's are interpreted as redundant)
  printf("value: %llu, with input: \"\\\\ 123\" \n",strtoull ("\\ 123", &pEnd, 10));//ull value = 0
  printf("value: %llu, with input: \"\\0 123\" \n",strtoull ("\0 123", &pEnd, 10));//ull value = 0 (as \0 signifies the end of the string)


  //Other ASCII whitespace charaters such as \n and \t are also procecced the same way ' ' is:
  printf("value: %llu, with input: \"\\n\\n123\\n\\n\" \n",strtoull ("\n\n123\n\n", &pEnd, 10)); //ull value = 123; pEnd points to '\n' after 3 (the first one, thats still within the string)

printf("errno value: %d\n",errno); errno=0;

  //The '-' character is processed as a negative number prefix, but creates an underflow as were converting into an UNSIGNED long long int
  printf("value: %llu, with input: \"-\" \n",strtoull ("-", &pEnd, 10));//ull value = 0; pEnd points to '-'
  printf("value: %llu, with input: \"-123\" \n",strtoull ("-123", &pEnd, 10));//ull value = 18446744073709551493; pEnd points to '' null string after the 3
  //another user error case that should be looked out for is one where a space is accidentally inserted between the '-' and the digits:
  printf("value: %llu, with input: \"- 123\" \n",strtoull ("- 123", &pEnd, 10));//ull value = 0; pEnd points to '-'
  

  //Looking at which values output errno == ERANGE on overflow:
  printf("value: %llu, with input: \"18446744073709551614\" \n",strtoull ("18446744073709551614", &pEnd, 10));//ull value = 18446744073709551614
  printf("value: %llu, with input: \"18446744073709551615\" \n",strtoull ("18446744073709551615", &pEnd, 10));//ull value = 18446744073709551615
  printf("errno value: %d\n",errno); errno=0;
  printf("value: %llu, with input: \"18446744073709551616\" \n",strtoull ("18446744073709551616", &pEnd, 10));//ull value = 18446744073709551615 -> errno == ERANGE
  printf("errno value: %d\n",errno); errno=0;
  printf("value: %llu, with input: \"20000000000000000000\" \n",strtoull ("20000000000000000000", &pEnd, 10));//ull value = 18446744073709551615 -> errno == ERANGE
  printf("errno value: %d\n",errno); errno=0;

  //ULLONG_MAX=18446744073709551615;
  
  //As can be seen in these cases, underflows do not set off errno == ERANGE:
  printf("value: %llu, with input: \"-1\" \n",strtoull ("-1", &pEnd, 10));//ull value = 18446744073709551615
  printf("value: %llu, with input: \"-2\" \n",strtoull ("-2", &pEnd, 10));//ull value = 18446744073709551614
  //...
  printf("value: %llu, with input: \"-18446744073709551614\" \n",strtoull ("-18446744073709551614", &pEnd, 10));//ull value = 2
  printf("value: %llu, with input: \"-18446744073709551615\" \n",strtoull ("-18446744073709551615", &pEnd, 10));//ull value = 1
  //unless the values are so negative that they cycle back into being overflows
  printf("errno value: %d\n",errno); errno=0;
  printf("value: %llu, with input: \"-18446744073709551616\" \n",strtoull ("-18446744073709551616", &pEnd, 10));//ull value = 18446744073709551615 -> errno == ERANGE
  printf("errno value: %d\n",errno); errno=0;
  printf("value: %llu, with input: \"-18446744073709551617\" \n",strtoull ("-18446744073709551617", &pEnd, 10));//ull value = 18446744073709551615 -> errno == ERANGE
  printf("errno value: %d\n",errno); errno=0;
  //check_leading_chars();
  return 0;
}

