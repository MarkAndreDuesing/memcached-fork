/* strtoull example */
#include <stdio.h>      /* printf, NULL */
#include <stdlib.h>     /* strtoull */

int main ()
{
  char szNumbers[] = "250068492 7b06af00 1100011011110101010001100000 0x6fffff";
  char * pEnd;
  unsigned long long int ulli1, ulli2, ulli3, ulli4;
  ulli1 = strtoull (szNumbers, &pEnd, 10);
  ulli2 = strtoull (pEnd, &pEnd, 16);
  ulli3 = strtoull (pEnd, &pEnd, 2);
  ulli4 = strtoull (pEnd, NULL, 0);
  printf ("The decimal equivalents are: %llu, %llu, %llu and %llu.\n", ulli1, ulli2, ulli3, ulli4);
  
  
  printf("value: %llu, \nwith input: \"123\" \n",strtoull ("123", &pEnd, 10));
  printf("value: %llu, \nwith input: \" 123\" \n",strtoull (" 123", &pEnd, 10));
  printf("value: %llu, \nwith input: \"123 \" \n",strtoull ("123 ", &pEnd, 10));//where does the adresse end in this case? Important testcase!
  
  printf("value: %llu, \nwith input: \"12A34\" \n",strtoull ("12A34", &pEnd, 10));
  printf("value: %llu, \nwith input: \"18446744073709551614\" \n",strtoull ("18446744073709551614", &pEnd, 10));
  printf("value: %llu, \nwith input: \"18446744073709551615\" \n",strtoull ("18446744073709551615", &pEnd, 10));
  printf("value: %llu, \nwith input: \"18446744073709551616\" \n",strtoull ("18446744073709551616", &pEnd, 10));
  printf("value: %llu, \nwith input: \"20000000000000000000\" \n",strtoull ("20000000000000000000", &pEnd, 10));
  printf("value: %llu, \nwith input: \"String\" \n",strtoull ("String", &pEnd, 10));
  //ULLONG_MAX;
  printf("value: %llu, \nwith input: \"-1\" \n",strtoull ("-1", &pEnd, 10));
  printf("value: %llu, \nwith input: \"-18446744073709551614\" \n",strtoull ("-18446744073709551614", &pEnd, 10));
  printf("value: %llu, \nwith input: \"-18446744073709551615\" \n",strtoull ("-18446744073709551615", &pEnd, 10));
  printf("value: %llu, \nwith input: \"-18446744073709551616\" \n",strtoull ("-18446744073709551616", &pEnd, 10));
  printf("value: %llu, \nwith input: \"-18446744073709551617\" \n",strtoull ("-18446744073709551617", &pEnd, 10));
  printf("value: %llu, \nwith input: \"0\" \n",strtoull ("0", &pEnd, 10));
  
  printf("value: %llu, \nwith input: \"000123\" \n",strtoull ("000123", &pEnd, 10));
  
  printf("value: %llu, \nwith input: \"\" \n",strtoull ("", &pEnd, 10));
  printf("value: %llu, \nwith input: \" \" \n",strtoull (" ", &pEnd, 10));
  printf("value: %llu, \nwith input: \"\\\\\" \n",strtoull ("\\", &pEnd, 10));
  printf("value: %llu, \nwith input: \"\\0\" \n",strtoull ("\0", &pEnd, 10));
  printf("value: %llu, \nwith input: \"\\n\" \n",strtoull ("\n", &pEnd, 10));
  //printf("value: %llu, \nwith input: \"NULL\" \n",strtoull (NULL, &pEnd, 10));
  
  printf("value: %llu, \nwith input: \"\\\\ 111\" \n",strtoull ("\\ 111", &pEnd, 10));
  printf("value: %llu, \nwith input: \"\\0 111\" \n",strtoull ("\0 111", &pEnd, 10));
  printf("value: %llu, \nwith input: \"\\n 111\" \n",strtoull ("\n 111", &pEnd, 10));
  
  printf("value: %llu, \nwith input: \"111\\\\\" \n",strtoull ("111\\", &pEnd, 10));
  printf("value: %llu, \nwith input: \"111\\0\" \n",strtoull ("111\0", &pEnd, 10));
  printf("value: %llu, \nwith input: \"111\\n\" \n",strtoull ("111\n", &pEnd, 10));
  
  return 0;
}