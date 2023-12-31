#include <stdio.h>
#include <stdlib.h>
#include <errno.h>

int main()
{
  char *pEnd;
  
  //Base cases:
  printf("value: %llu, with input: \"\" \n",strtoull ("", &pEnd, 10));//ull value = 0; pEnd points to ''
  //printf("value: %llu, \nwith input: NULL \n",strtoull (NULL, &pEnd, 10));//-> Segmentation fault (core dumped)
  printf("value: %llu, with input: \" \" \n",strtoull (" ", &pEnd, 10));//ull value = 0; pEnd points to ' '
  printf("value: %llu, with input: \"A\" \n",strtoull ("A", &pEnd, 10));//ull value = 0; pEnd points to 'A'
  
  printf("value: %llu, with input: \"123\" \n",strtoull ("123", &pEnd, 10)); //ull value = 123; pEnd points to '' null string after 3
  printf("value: %llu, with input: \" 123\" \n",strtoull (" 123", &pEnd, 10)); //ull value = 123; pEnd points to '' null string after 3
  printf("value: %llu, with input: \"123 \" \n",strtoull ("123 ", &pEnd, 10)); //ull value = 123; pEnd points to ' ' empty space after 3 (the first one, thats still within the string)
  
  printf("value: %llu, with input: \"000123\" \n",strtoull ("000123", &pEnd, 10));//ull value = 123 (leading 0's are interpreted as redundant)
  printf("value: %llu, with input: \"\\\\ 123\" \n",strtoull ("\\ 123", &pEnd, 10));//ull value = 0
  printf("value: %llu, with input: \"\\0 123\" \n",strtoull ("\0 123", &pEnd, 10));//ull value = 0 (as \0 signifies the end of the string)


  //Other ASCII whitespace charaters such as \n and \t are also procecced the same way ' ' is:
  printf("value: %llu, with input: \"\\n\\n123\\n\\n\" \n",strtoull ("\n\n123\n\n", &pEnd, 10)); //ull value = 123; pEnd points to '\n' after 3 (the first one, thats still within the string)


  //The '-' character is processed as a negative number prefix, but creates an underflow as were converting into an UNSIGNED long long int
  printf("value: %llu, with input: \"-\" \n",strtoull ("-", &pEnd, 10));//ull value = 0; pEnd points to '-'
  printf("value: %llu, with input: \"-123\" \n",strtoull ("-123", &pEnd, 10));//ull value = 18446744073709551493; pEnd points to '' null string after the 3
  //another user error case that should be looked out for is one where a space is accidentally inserted between the '-' and the digits:
  printf("value: %llu, with input: \"- 123\" \n",strtoull ("- 123", &pEnd, 10));//ull value = 0; pEnd points to '-'
  

  //Looking at which values output errno == ERANGE on overflow:
  printf("value: %llu, with input: \"18446744073709551614\" \n",strtoull ("18446744073709551614", &pEnd, 10));//ull value = 18446744073709551614
  printf("value: %llu, with input: \"18446744073709551615\" \n",strtoull ("18446744073709551615", &pEnd, 10));//ull value = 18446744073709551615
  printf("value: %llu, with input: \"18446744073709551616\" \n",strtoull ("18446744073709551616", &pEnd, 10));//ull value = 18446744073709551615 -> errno == ERANGE
  printf("value: %llu, with input: \"20000000000000000000\" \n",strtoull ("20000000000000000000", &pEnd, 10));//ull value = 18446744073709551615 -> errno == ERANGE
  //ULLONG_MAX=18446744073709551615;
  
  //As can be seen in these cases, underflows do not set off errno == ERANGE:
  printf("value: %llu, with input: \"-1\" \n",strtoull ("-1", &pEnd, 10));//ull value = 18446744073709551615
  printf("value: %llu, with input: \"-2\" \n",strtoull ("-2", &pEnd, 10));//ull value = 18446744073709551614
  //...
  printf("value: %llu, with input: \"-18446744073709551614\" \n",strtoull ("-18446744073709551614", &pEnd, 10));//ull value = 2
  printf("value: %llu, with input: \"-18446744073709551615\" \n",strtoull ("-18446744073709551615", &pEnd, 10));//ull value = 1
  //unless the values are so negative that they cycle back into being overflows
  printf("value: %llu, with input: \"-18446744073709551616\" \n",strtoull ("-18446744073709551616", &pEnd, 10));//ull value = 18446744073709551615 -> errno == ERANGE
  printf("value: %llu, with input: \"-18446744073709551617\" \n",strtoull ("-18446744073709551617", &pEnd, 10));//ull value = 18446744073709551615 -> errno == ERANGE

  return 0;
}

