#include <stdio.h>
#include <ctype.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>

#include <stdbool.h>//why do i need this when it wasnt needed in the original util.c?

#include <assert.h>

#include <limits.h>

void reach_error() { assert(0); } //this is just the same as directly writing assert(0); in the main code?
unsigned int minimum(unsigned int a,unsigned int b);

static bool safe_strcpy(char *dst, const char *src, const size_t dstmax); //https://stackoverflow.com/questions/8440816/message-warning-implicit-declaration-of-function


//verification harness (arrange-act-assert):
extern unsigned int __VERIFIER_nondet_uint();
extern char __VERIFIER_nondet_char();

int main(){


//Encode Precondition (Arrange):

	unsigned int sizeDst = __VERIFIER_nondet_uint();
    //unsigned int sizeDst = UINT_MAX;
	if(sizeDst >= 15 || sizeDst <= 3) {abort();} //in this case sizeDst cant be smaller than 0, because were using unsigned int
	char dst[sizeDst];

	unsigned int sizeSrc = __VERIFIER_nondet_uint();
    //unsigned int sizeSrc = UINT_MAX-1;
	if(sizeSrc >= 15 || sizeSrc <= 3) {abort();}
	char src[sizeSrc];

	//if(dst == 0 || src == 0) { abort(); }


	//unsigned int sizeDst = 10;
	//char dst[sizeDst];

	//unsigned int sizeSrc = 20;
	//char src[sizeSrc];


//Main Verification Harness:

	for(unsigned int i = 0; i < ((i < sizeDst-1)&&(i < sizeSrc-1)); i++) {//could also do just: i < sizeDst-1
		src[i] = __VERIFIER_nondet_char(); 
		//src[i] = 'a'; 
	}
	src[minimum(sizeDst-1,sizeSrc-1)] = '\0';//were filling up src to the maximum size of dst or src, whichever comes first
	//could also do just: src[sizeDst-1] = '\0'; 

	safe_strcpy(dst, src, sizeDst);

//Encode Postcondition (Assert):
	if(dst[0] != src[0]) {
        printf("assert(false)\n");
		reach_error();
	}
	return 0;
}


bool safe_strcpy(char *dst, const char *src, const size_t dstmax) {
   size_t x;

   for (x = 0; x < dstmax - 1 && src[x] != '\0'; x++) {
        dst[x] = src[x];
   }

   dst[x] = '\0';

   if (src[x] == '\0') {
        printf("true\n");
        return true;
   } else {
        assert(dst[x] != src[x]);//redundant with main() postcondition assertion? but i get different errors if i leave it out. no they are different! x instead of 0
        //the alternative error i get when leaving this out is that src = 0, and thereby get a NULL pointer when i try to do src[i] = __VERIFIER_nondet_char();?
        printf("false\n");
        return false;
   }
}

unsigned int minimum(unsigned int a,unsigned int b){
	if(a<=b){return a;}
	else{return b;}
}

// x is a locally declared variable that starts at 0
//dstmax is the length of the string/character list to be copied? or the maximum length of the resulting string to be copied to?
//src is the string to be copied from?
//dst is the string to be copied to?

//z.B.:
//dstmax=4
//x=0; x=1; x=2
//src[] = [a,b,c,d,e,f,\0]
//-> dst[] = [a,b,c] -> after loop: dst[] = [a,b,c,\0] -> src[3]='d' != '\0'=dst[3] -> return 0, which is fine because src="abcdef" isnt actualy equal to dst="abc"


//z.B.:
//dstmax=4
//x=0; x=1 because src[2]='\0'
//src[] = [a,b,\0]
//-> dst[] = [a,b] -> after loop: dst[] = [a,b,\0] -> src[2]='b' == 'b'=dst[2] -> return 1. If we didnt have src[x] != '\0' in the for loop clause, we would have an error because of array length?

//z.B.:
//dstmax=4
//x=0; x=1; x=2
//src[] = [a,b,c,\0]
//-> dst[] = [a,b,c] -> after loop: dst[] = [a,b,c,\0] -> src[3]='\0' == '\0'=dst[3] -> return 1, correct as they are the same string

//-> logically this also implies dstmax := the array length of dst[] including \0
// so the point of safe_strcpy is to limit the maximum length of the text that can be copied to equal or less than the limit dstmax


//i think the problem in Ultimate Automiser was thatdst could theoretically be empty, which would lead to an error?



// gcc safe_strcpy.c -o safe_strcpy.exe
// ./safe_strcpy.exe



//vorschlag: bei aenderungen vom code, nicht die selbe datei nochmal veraendern, sondern neue datei erstellen -> git um history von datei/testaenderungen zu haben
// am meisten jeweils pro testziel unterteilen. z.B. harness_safe_strcpy_simple.c, harness_safe_strcpy_all_non_det.c, harness_safe_strcpy_dest_and_source_same_size.c
//	whoops, probably should have done that already


//terminal command um versionen zu verwalten:
//cp util.c util_firstExample_safe_strcpy.c
//git checkout -- util.c
//git add util_firstExample_safe_strcpy.c
//git commit -m "Harness for safe_strcpy with concrete inputs"

//man kann auch in der bachelorarbeit die bearbeitete file verlinken (vermutlich ueber github)