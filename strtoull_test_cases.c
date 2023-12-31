/* strtoull example */
#include <stdio.h>      /* printf, NULL */
#include <stdlib.h>     /* strtoull */
//#include <assert.h>
#include <errno.h>

int main()
{
  char *pEnd; unsigned long long int temp;
  
  printf("value: %llu, \nwith input: \"\" \n",strtoull ("", &pEnd, 10));//ull value = 0; pEnd points to ''
  //printf("value: %llu, \nwith input: NULL \n",strtoull (NULL, &pEnd, 10));//-> Segmentation fault (core dumped)
  printf("value: %llu, \nwith input: \" \" \n",strtoull (" ", &pEnd, 10));//ull value = 0; pEnd points to ' '
  printf("value: %llu, \nwith input: \"A\" \n",strtoull ("A", &pEnd, 10));//ull value = 0; pEnd points to 'A'

  
  char tempstr[] = "- 123";//char tempstr[] = "  123  ";
  printf("tempstr     :%p, *tempstr      :'%c'\n",tempstr, *tempstr); 
  printf("tempstr+1   :%p, *(tempstr+1)  :'%c'\n",tempstr+1, *(tempstr+1)); 
  printf("tempstr+2   :%p, *(tempstr+2)  :'%c'\n",tempstr+2, *(tempstr+2)); 
  printf("tempstr+3   :%p, *(tempstr+3)  :'%c'\n",tempstr+3, *(tempstr+3)); 
  printf("tempstr+4   :%p, *(tempstr+4)  :'%c'\n",tempstr+4, *(tempstr+4)); 
  printf("tempstr+5   :%p, *(tempstr+5)  :'%c'\n",tempstr+5, *(tempstr+5));
  printf("tempstr+6   :%p, *(tempstr+6)  :'%c'\n",tempstr+6, *(tempstr+6)); 
  printf("tempstr+7   :%p, *(tempstr+7)  :'%c'\n",tempstr+7, *(tempstr+7));
  printf("&tempstr+1  :%p, *(&tempstr+1) :'%c'\n",&tempstr+1, *(&tempstr+1)); 
  

  printf("value: %llu, \nwith input: \"123\" \n",strtoull ("123", &pEnd, 10)); //ull value = 123; pEnd points to '' null string after 3
  printf("value: %llu, \nwith input: \" 123\" \n",strtoull (" 123", &pEnd, 10)); //ull value = 123; pEnd points to '' null string after 3
  printf("value: %llu, \nwith input: \"123 \" \n",strtoull ("123 ", &pEnd, 10)); //ull value = 123; pEnd points to ' ' empty space after 3 (the first one, thats still within the string)
  
  //Other ASCII whitespace charaters such as \n and \t are also procecced the same way ' ' is:
  printf("value: %llu, \nwith input: \"\\n\\n123\\n\\n\" \n",strtoull ("\n\n123\n\n", &pEnd, 10)); //ull value = 123; pEnd points to '\n' after 3 (the first one, thats still within the string)

  //The '-' character is processed as a negative number prefix, but creates an underflow as were converting into an UNSIGNED long long int
  printf("value: %llu, \nwith input: \"-\" \n",strtoull ("-", &pEnd, 10));//ull value = 0; pEnd points to '-'
  printf("value: %llu, \nwith input: \"-123\" \n",strtoull ("-123", &pEnd, 10));//ull value = 18446744073709551493; pEnd points to '' null string after the 3
  //another user error case that should be looked out for is one where a space is accidentally inserted between the '-' and the digits:
  printf("value: %llu, \nwith input: \"- 123\" \n",strtoull ("- 123", &pEnd, 10));//ull value = 0; pEnd points to '-'
  
  //printf("\n%p",pEnd);

  //strtoull can also be used sequentially, although we never do that here:
  /*
  printf("\n\n");
  char szNumbers[] = "12 34";
  temp = strtoull (szNumbers, &pEnd, 10); printf("value: %llu, with input: \"%s\"; Following values: *pEnd:'%c', *(pEnd+1):'%c'  \n",temp,szNumbers,*pEnd,*(pEnd+1));
  temp = strtoull (pEnd, &pEnd, 10); printf("value: %llu, with input: \"%s\"; Following values: *pEnd:'%c', *(pEnd+1):'%c' (second segment)\n",temp,szNumbers,*pEnd,*(pEnd+1));
  */

/*
  printf("\n\n");
  char szNumbers2[] = "- 25";//14 \0 25
  temp = strtoull (szNumbers2, &pEnd, 10); printf("value: %llu, with input: \"%s\"; Following values: *pEnd:'%c', *(pEnd+1):'%c'  \n",temp,szNumbers2,*pEnd,*(pEnd+1));
  temp = strtoull (pEnd, &pEnd, 10); printf("value: %llu, with input: \"%s\"; Following values: *pEnd:'%c', *(pEnd+1):'%c' (second segment)\n",temp,szNumbers2,*pEnd,*(pEnd+1));
*/

  //"12 34" same effect as for "12  34" (double space). still points to the space directly after 12 when done reading, not the second space after 12
  //"12- 34" leads to 12 being read, then - being read, leading to value 0, then 34

  //space seems to be the only character thats repeatedly removed, all others are only removed once per call of strtoull. e.g. "12pp34" will point to the first p after, then get stuck on that after repeated calls

//only need to regard base 10
//explain the inputs, what they represent and how they change
//https://cplusplus.com/reference/cstdlib/strtoull/
//https://codeforwin.org/c-programming/convert-string-to-unsigned-long-long-using-strtoull-c
//explain that anything except for escape characters like \n or ' ' lead do block (check what all the allowed characters are)
//and one '-' in a row is allowed unblocked, despite the underflow it creates
//what if theres an unsafe single '\' in the string block
//also a '\0 'ends the input even if theres more after, leading to potentially unprocecced results


  printf("value     : %llu, with input: \"18446744073709551614\" \n",strtoull ("18446744073709551614", &pEnd, 10));//ull value = 18446744073709551614
  printf("value     : %llu, with input: \"18446744073709551615\" \n",strtoull ("18446744073709551615", &pEnd, 10));//ull value = 18446744073709551615
  printf("value     : %llu, with input: \"18446744073709551616\" \n",strtoull ("18446744073709551616", &pEnd, 10));//ull value = 18446744073709551615 -> errno == ERANGE
  printf("value     : %llu, with input: \"20000000000000000000\" \n",strtoull ("20000000000000000000", &pEnd, 10));//ull value = 18446744073709551615 -> errno == ERANGE
  //ULLONG_MAX=18446744073709551615;

  //printf("errno value: %d\n",errno); errno=0;
  
  //As can be seen here underflows do not set off errno == ERANGE:
  printf("value     : %llu, with input: \"-1\" \n",strtoull ("-1", &pEnd, 10));//ull value = 18446744073709551615
  printf("value     : %llu, with input: \"-2\" \n",strtoull ("-2", &pEnd, 10));//ull value = 18446744073709551614
  //...
  printf("value     : %llu, with input: \"-18446744073709551614\" \n",strtoull ("-18446744073709551614", &pEnd, 10));//ull value = 2
  printf("value     : %llu, with input: \"-18446744073709551615\" \n",strtoull ("-18446744073709551615", &pEnd, 10));//ull value = 1
  //unless the values are so negative that they cycle back into being overflows
  printf("value     : %llu, with input: \"-18446744073709551616\" \n",strtoull ("-18446744073709551616", &pEnd, 10));//ull value = 18446744073709551615 -> errno == ERANGE
  printf("value     : %llu, with input: \"-18446744073709551617\" \n",strtoull ("-18446744073709551617", &pEnd, 10));//ull value = 18446744073709551615 -> errno == ERANGE

  
  printf("value     : %llu, \nwith input: \"000123\" \n",strtoull ("000123", &pEnd, 10));//ull value = 123 (leading 0's are interpreted as redundant)
  
  //printf("value     : %llu, \nwith input: \"\" \n",strtoull ("", &pEnd, 10));
  //printf("value     : %llu, \nwith input: \" \" \n",strtoull (" ", &pEnd, 10));
  //printf("value     : %llu, \nwith input: \"\\\\\" \n",strtoull ("\\", &pEnd, 10));
  //printf("value     : %llu, \nwith input: \"\\0\" \n",strtoull ("\0", &pEnd, 10));
  //printf("value     : %llu, \nwith input: \"\\n\" \n",strtoull ("\n", &pEnd, 10));
  //printf("value: %llu, \nwith input: \"NULL\" \n",strtoull (NULL, &pEnd, 10));
  
  printf("value     : %llu, \nwith input: \"\\\\ 123\" \n",strtoull ("\\ 123", &pEnd, 10));//ull value = 123
  printf("value     : %llu, \nwith input: \"\\0 123\" \n",strtoull ("\0 123", &pEnd, 10));//ull value = 123
  printf("value     : %llu, \nwith input: \"\\n 123\" \n",strtoull ("\n 123", &pEnd, 10));//ull value = 123
  
  //printf("value     : %llu, \nwith input: \"111\\\\\" \n",strtoull ("111\\", &pEnd, 10));
  //printf("value     : %llu, \nwith input: \"111\\0\" \n",strtoull ("111\0", &pEnd, 10));
  //printf("value     : %llu, \nwith input: \"111\\n\" \n",strtoull ("111\n", &pEnd, 10));


  return 0;
}

int main2 ()
{
  char szNumbers[] = "-100 18446744073709551615 18446744073709551616 9999999999999999999 99999999999999999999";
  //char szNumbers[] = "-100";
  char * pEnd;
  
  //-100 -> errno != ERANGE
  //18446744073709551615 -> errno != ERANGE
  //18446744073709551616 -> errno == ERANGE
  //9999999999999999999 -> errno != ERANGE
  //99999999999999999999 -> errno == ERANGE

  unsigned long long int ulli1, ulli4, ulli5/*, ulli6, ulli7*/;
  
  ulli1 = strtoull (szNumbers, &pEnd, 10);
  ulli4 = strtoull (pEnd, &pEnd, 10);
  ulli5 = strtoull (pEnd, &pEnd, 10);
  //ulli6 = strtoull (pEnd, &pEnd, 10);
  //ulli7 = strtoull (pEnd, &pEnd, 10);
  printf ("The decimal equivalents are: %llu, %llu, %llu.\n", ulli1, ulli4, ulli5/*, ulli6, ulli7*/);
  
  if(errno != ERANGE){printf("errno != ERANGE\n");} else {printf("errno == ERANGE\n");}
  
  return 0;
}

/*
Output:
The decimal equivalents are: 18446744073709551516.
errno != ERANGE
*/


int main3 ()
{
  char szNumbers[] = "250068492 777";
  char *pEnd;
  unsigned long long int ulli1;
  ulli1 = strtoull (szNumbers, &pEnd, 10);
  printf("a: '%s'\n",pEnd);//it stops at the last digit, before the newline, so the space is at the beginning of the next segement, and thereby the first char that pEnd points to!
  printf("b: '%c' %d\n",*pEnd,*pEnd);
  printf("c: %llu\n", ulli1);
  return 0;
}

/*
output:
a: ' 7b06af00 1100011011110101010001100000 0x6fffff'
b: ' ' 32
c: 250068492
*/


//what happens with 2 spaces in a row, like "1  2"?
//what about "1-2"?