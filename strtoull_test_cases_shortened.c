#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>


// Function to add a character to the beginning of a string
void addCharToBeginning(char ch, const char *original, char *result) {
    // Add the character to the beginning
    result[0] = ch;

    // Copy the original string to the new string starting from index 1
    strcpy(result + 1, original);
}

void appendString(char **str, char c) {
    //Credit: taken from Chat-GPT 
    size_t currentLength = *str ? strlen(*str) : 0;
    *str = realloc(*str, currentLength + 2);  //Allocate memory for the new character -> +2 to accommodate the new character and the null terminator
    (*str)[currentLength] = c;
    (*str)[currentLength + 1] = '\0';
}


int check_leading_chars(){
  //char temp_char = 0;
  /*
  for (int k = 0; k < 128; k++) {
	    char ch = k;
      char str_temp[2]={ch,'\0'};
	    strcat(str_temp,"123");
      printf("%s", str_temp);
	}
  */
  char *originalString = "123";
  char *myString1 = NULL;	


  for (int k = 0; k < 128; k++) {
	    char ch = k;
      
      char resultString[strlen(originalString) + 2];
      // Declare a static array for the result string (original length + 2 for the added character and null terminator)
      addCharToBeginning(ch,"123",resultString);
      printf("added prefix char: '%c' ; final string: %s\n", ch, resultString);

      printf("value: %llu, with input: \"%s\"\n",strtoull (resultString, NULL, 10), resultString);
      if(strtoull (resultString, NULL, 10) != 0){
        appendString(&myString1, ch);
        }
  }
  printf("\n\n\n");
  for (int k = 0; k < strlen(myString1); k++) {printf(" digit:'%d', char:'%c'\n", myString1[k], myString1[k]);}
  //-> strtoull is just like isspace with its interpretation of whitespace characters, accepting char:9-13,32 and then additionally 43 for '-', 45 for '+' and 48-57 for the digits 0-9


  //check if i can have multiple of these whitespaces and '-' or '+' leading:
  printf("value: %llu, with input: \"\\t\\n123\" \n",strtoull ("\t\t123", NULL, 10)); //-> ull = 123
  printf("value: %llu, with input: \"\\n\\n123\" \n",strtoull ("\n\n123", NULL, 10)); //-> ull = 123
  printf("value: %llu, with input: \"\\v\\n123\" \n",strtoull ("\v\v123", NULL, 10)); //-> ull = 123
  printf("value: %llu, with input: \"\\f\\n123\" \n",strtoull ("\f\f123", NULL, 10)); //-> ull = 123
  printf("value: %llu, with input: \"  123\" \n",strtoull ("  123", NULL, 10)); //-> ull = 123
  printf("value: %llu, with input: \"--123\" \n",strtoull ("--123", NULL, 10)); //-> ull = 0
  printf("value: %llu, with input: \"++123\" \n",strtoull ("++123", NULL, 10)); //-> ull = 0
  //can have multiple leading whitespaces of any kind, but not - or +
  //but i can have a whitespace, then a - or a +:
  printf("value: %llu, with input: \" -123\" \n",strtoull (" -123", NULL, 10)); //-> ull = 18446744073709551493
  printf("value: %llu, with input: \" +123\" \n",strtoull (" +123", NULL, 10)); //-> ull = 123

  return 1;
}






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

  //chech whitespace characters
  printf("value: %llu, with input: \"\\n123 \" \n",strtoull ("\n123", &pEnd, 10)); //ull value = 123; pEnd points to ' ' empty space after 3 (the first one, thats still within the string)
  printf("value: %llu, with input: \"\\t123 \" \n",strtoull ("\t123", &pEnd, 10)); //ull value = 123; pEnd points to ' ' empty space after 3 (the first one, thats still within the string)
  
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
  
  check_leading_chars();
  return 0;
}

