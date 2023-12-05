#include <stdio.h>
#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>

#include <stdint.h>//for uint64_t
#include <stdbool.h>//for bool

#define xisspace(c) isspace((unsigned char)c)
//A type char without a signed or unsigned qualifier may behave as either a signed or unsigned char; 
//which makes more sense here, as: isspace(char c) takes a char type as its input. meaning it could be either?
//but *endptr is a char type, isnt it?
//https://stackoverflow.com/questions/2054939/is-char-signed-or-unsigned-by-default/2054941#2054941
//https://stackoverflow.com/questions/436513/char-signed-char-char-unsigned-char

static char *uriencode_map[256];
static char uriencode_str[768];

bool safe_strtoull(const char *str, uint64_t *out) {
    //how does the length of a uint64_t compare to a long long?
    //A synonym for the unsigned long long type is uint64. according to https://rambutan.readthedocs.io/projects/librambutan/en/latest/lang/cpp/unsignedlonglong.html
    assert(out != NULL);
    errno = 0;
    *out = 0;//what is the point of this method input, if its just overwritten with 0?
    //the point is it comes in as whatever and returns the potentially successful stroull value, or 0. Like a second return value besides the bool?
    //could make some assertions about its resulting value
    // understand why we need *out, and it cant just be uint_64 out. Because out is an adresse, even if the adresse itself is never directly used here
    char *endptr;
    unsigned long long ull = strtoull(str, &endptr, 10);
    //the predrefined strtoull method also changes errno (without even needing it as an input? some sort of C convention?)
    if ((errno == ERANGE) || (str == endptr)) {
        //str == endptr would be the case if the string is just whitespaces? check!!!
        //according to some stackoverflow side remark: "i.e. the input string was empty, or only contained whitespace, 
        //or the first non-whitespace character was not valid"

        //and (errno == ERANGE) would occur if the unsigned long long is out of range (would usually be an overflow, but instead returns the MAX/MIN value)?
        return false;
    }

    if (xisspace(*endptr) || (*endptr == '\0' && endptr != str)) { //str != endptr is guaranteed true because of the previous if loop, isnt it?
    //xisspace(*endptr) would be the case if the value at the adresse endptr is a whitespace
    //(*endptr == '\0' && endptr != str) would be the case if the value at adresse endptr is \0 (as would be the case at the end of a string), 
    //but the string isnt all whitespaces?

    //xisspace -> check again what happens when you typecast a char as an unsigned char, especially if out of range

        if ((long long) ull < 0) {
            /* only check for negative signs in the uncommon case when
             * the unsigned number is so big that it's negative as a
             * signed number. */
        //so to check for the case of massive numbers wrapping back around to negative if they were unsigned

        //check again what happens when you typecast an unsigned long long as a long long

            if (memchr(str, '-', endptr - str) != NULL) {
            //so youre checking if the char '-' (the minus sign) turns up between the start of (the adresse of) the string and the endptr (adresse)
            //(if it does you return the adresse of where that - was found?)
                return false;
            //so point is, this is a safety check, as memchr(str, '-', endptr - str) should be NULL as '-' should not occur between the str and endptr adresses
            
            //why only check for this if (long long) ull < 0
            //i guess the idea is, if strtoull read a negative value, and automatically converted it into a very large one, because of the unsigned part of its definition 
            //-> we convert the very large number back to see if its negative, and if it is, we check whether the string given to us had a '-' minus 
            //-> if it does, return false because strtoull outputs unsigned long long and shouldnt be dealing with negative numbers

            //the alternative case is where we actually read a massive number for strtoull, not a negative one, so '-' wont appear in the string, and everything was done correctly
            //prove this with a witness and an else{assert(...)}?
            }
        }
        *out = ull;
        return true;
    }
    return false;
    //safe_strtoull also never inputs  oroutputs the &endptr value, so becase of the black box nature we cant really use it 
    //repeatedly use it on the same string, the way we could with strtoull

//out of interest rewrite this with compacted if/else clauses, rather than just if -> return; also useful for assertions about reachability
}

//in command prompt:
//gcc -o safe_strtoull_harness safe_strtoull_harness.c
//safe_strtoull_harness


//https://github.com/memcached/memcached/blob/9723c0ea8ec1237b8364410ba982af8ea020a2b6/util.c#L49
//https://www.tutorialspoint.com/c_standard_library/c_function_memchr.htm
//https://www.tutorialspoint.com/c_standard_library/c_function_isspace.htm
//https://cplusplus.com/reference/cstdlib/strtoull/
//https://cplusplus.com/reference/cstdlib/strtol/  //watchout, works a little differently, but explained more
//https://stackoverflow.com/questions/5493235/strtol-returns-an-incorrect-value

//https://cpp.sh/?source=%2F*+strtol+example+*%2F%0D%0A%23include+%3Cstdio.h%3E++++++%2F*+printf+*%2F%0D%0A%23include+%3Cstdlib.h%3E+++++%2F*+strtol+*%2F%0D%0A%0D%0Aint+main+()%0D%0A%7B%0D%0A++%2F%2Fchar+szNumbers%5B%5D+%3D+%22250068492+60c0c0+-1101110100110100100000+0x6fffff%22%3B%0D%0A++++++++%2F%2FThe+decimal+equivalents+are%3A+250068492%2C+6340800%2C+-3624224+and+7340031.%0D%0A++%2F%2Fchar+szNumbers%5B%5D+%3D+%2225006800492+60c0c0+-1101110100110100100000+0x6fffff%22%3B%0D%0A++++++++%2F%2FThe+decimal+equivalents+are%3A+2147483647%2C+6340800%2C+-3624224+and+7340031.%0D%0A++%2F%2Fchar+szNumbers%5B%5D+%3D+%22250068f492+60c0c0+-1101110100110100100000+0x6fffff%22%3B%0D%0A++++++++%2F%2FThe+decimal+equivalents+are%3A+250068%2C+62610%2C+0+and+60.%0D%0A++%2F%2Fchar+szNumbers%5B%5D+%3D+%22250068f00492+60c0c0+-1101110100110100100000+0x6fffff%22%3B%0D%0A++++++++%2F%2FThe+decimal+equivalents+are%3A+250068%2C+15729810%2C+0+and+60.%0D%0A++%2F%2Fchar+szNumbers%5B%5D+%3D+%22250068+f00492+60c0c0+-1101110100110100100000+0x6fffff%22%3B%0D%0A++++++++%2F%2FThe+decimal+equivalents+are%3A+250068%2C+15729810%2C+0+and+60.%0D%0A++%2F%2Fchar+szNumbers%5B%5D+%3D+%22250068-f00492+60c0c0+-1101110100110100100000+0x6fffff%22%3B%0D%0A++++++++%2F%2FThe+decimal+equivalents+are%3A+250068%2C+-15729810%2C+0+and+60.%0D%0A++char+szNumbers%5B%5D+%3D+%22250068+-f00492+60c0c0+-1101110100110100100000+0x6fffff%22%3B%0D%0A++++++++%2F%2FThe+decimal+equivalents+are%3A+250068%2C+-15729810%2C+0+and+60.%0D%0A++char+*+pEnd%3B%0D%0A++long+int+li1%2C+li2%2C+li3%2C+li4%3B%0D%0A++li1+%3D+strtol+(szNumbers%2C%26pEnd%2C10)%3B%0D%0A++li2+%3D+strtol+(pEnd%2C%26pEnd%2C16)%3B%0D%0A++li3+%3D+strtol+(pEnd%2C%26pEnd%2C2)%3B%0D%0A++li4+%3D+strtol+(pEnd%2CNULL%2C0)%3B%0D%0A++printf+(%22The+decimal+equivalents+are%3A+%25ld%2C+%25ld%2C+%25ld+and+%25ld.%5Cn%22%2C+li1%2C+li2%2C+li3%2C+li4)%3B%0D%0A++return+0%3B%0D%0A%7D

//https://en.wikipedia.org/wiki/C_data_types
//https://www.geeksforgeeks.org/data-types-in-c/

//https://www.geeksforgeeks.org/maximum-value-of-unsigned-long-long-int-in-c/

//https://stackoverflow.com/questions/5836329/how-many-bytes-is-unsigned-long-long

//https://stackoverflow.com/questions/36074422/why-cant-you-just-check-if-errno-is-equal-to-erange
///https://stackoverflow.com/questions/1694164/is-errno-thread-safe
//https://www.alphacodingskills.com/c/notes/c-errno-erange.php
//https://www.tutorialspoint.com/c_standard_library/c_macro_erange.htm


//notes+#include <stdint.h>, #include <stdbool.h> added