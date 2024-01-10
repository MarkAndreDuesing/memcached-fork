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

//needed implicit declarations
extern unsigned int __VERIFIER_nondet_uint();
extern uint64_t __VERIFIER_nondet_ulonglong();
extern char __VERIFIER_nondet_char(); 
//static bool safe_strtoull(const char *str, uint64_t *out);
extern unsigned long long int strtoull (const char *__restrict __nptr, char **__restrict __endptr, int __base);

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
    //the predrefined strtoull method also changes errno (without even needing it as an input)
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
            //understand the difference between the string being something like "-531" and one of the individual char characters being '-56'
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
    //safe_strtoull also never inputs  or outputs the &endptr value, so becase of the black box nature we cant really use it 
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







int main(){


//Encode Precondition (Arrange):

//check for inputs by seeing where strtoull is used in memcached
//check for how delta, pr, _meta_flags, request[] and token[] definitions work
    //uint64_t req_cas_id = 0;
    //safe_strtoull(&pr->request[pr->token[5]],&req_cas_id)

    //uint64_t delta;
    //safe_strtoull(&pr->request[pr->tokens[i]+1],&delta)

    //safe_strtoull(&pr->request[pr->tokens[i]+1], &of->initial)

    //&of is an instance of _meta_flags

    //uint64_t value;
    //ptr = ITEM_data(it);
    //safe_strtoull(ptr,&value)
//understand where ITEM_data(it) is defined and how its used
//from memcached.h:
/**
* item is used to hold an item structure created after reading the command
* line of set/add/replace commands, but before we finished reading the actual
* data. The data is read into ITEM_data(item) to avoid extra copying.
*/
//#define ITEM_data(item) ((char*) &((item)->data) + (item)->nkey + 1 \
//     + (((item)->it_flags & ITEM_CFLAGS) ? sizeof(client_flags_t) : 0) \
//     + (((item)->it_flags & ITEM_CAS) ? sizeof(uint64_t) : 0))

//so I think we just take the (item)->data from ptr, with data being defined as union{uint64_t cas; char end;} data[];
//logically i assume we only take the uint64_t cas part of the string and return it with our *out
//also keep in mind ITEM_get_cas and ITEM_set_cas in this regard
    
    //char *val;
    //restart_get_kv(ctx, &key, &val);
    //uint64_t bigval_uint = 0;
    //safe_strtoull(val, &bigval_uint);
//watch out! restart_get_kv reads in a line and sets &val to (the end of?) the adresse of that line as a string.
//this val is then used in the various _mc_meta_load_cb switch cases of strtoull


	unsigned int sizeStr = __VERIFIER_nondet_uint();
    //unsigned int sizeDst = UINT_MAX;
	if(sizeStr >= 15 || sizeStr <= 3) {abort();} //in this case sizeDst cant be smaller than 0, because were using unsigned int
	char str[sizeStr];

    uint64_t strVal = __VERIFIER_nondet_ulonglong();
    if(strVal >= 50 || strVal <= 3) {abort();}


//Main Verification Harness:

    for(unsigned int i = 0; i < sizeStr-1; i++) {//fill up the string fully with random chars
		str[i] = __VERIFIER_nondet_char(); 
		//src[i] = ' '; 
	}
	str[sizeStr-1] = '\0';

    bool safe = safe_strtoull(str,&strVal);
    //safe_strtoull(const char *str, uint64_t *out)

	//safe_strcpy(dst, src, sizeDst);
    //safe_strcpy(char *dst, const char *src, const size_t dstmax);

//Encode Postcondition (Assert):
	
    //if(dst[0] != src[0]) {
    //    printf("assert(false)\n");
	//	reach_error();
	//}

    if(safe){
        return 1;
    } else{
	    return 0;
    }
}


//helpful note from memcached/proxy_internal.c:
    // TODO (v2): these safe_str* functions operate on C _strings_, but these
    // tokens simply end with a space or carriage return/newline, so we either
    // need custom functions or validate harder that these calls won't bite us
    // later.


/*
a context safe_strtoull is used in is:
for (i = start; i < pr->ntokens; i++) {
        uint8_t o = (uint8_t)pr->request[pr->tokens[i]];
        // zero out repeat flags so we don't over-parse for return data.
        if (o >= 127 || seen[o] != 0) {
            *errstr = "CLIENT_ERROR duplicate flag";
            return -1;
        }
        seen[o] = 1;
        switch (o) {
        ...
case 'C': // mset, mdelete, marithmetic
                if (!safe_strtoull(&pr->request[pr->tokens[i]+1], &of->req_cas_id)) {
                    *errstr = "CLIENT_ERROR bad token in command line format";
                    of->has_error = true;
                } else {
                    of->has_cas = true;
                }
                break;
Here its basically an error check with the side effect of changing the value of &of->req_cas_id. Watch out for this, 
as safe_strtoull generally produces hard to see side effects this way
*/

/*
Intended functionality of safe_strtoull from testapp.c:
static enum test_return test_safe_strtoull(void) {
    uint64_t val;
    assert(safe_strtoull("123", &val));
    assert(val == 123);
    assert(safe_strtoull("+123", &val));
    assert(val == 123);
    assert(!safe_strtoull("", &val));  // empty
    assert(!safe_strtoull("123BOGUS", &val));  // non-numeric
    assert(!safe_strtoull("92837498237498237498029383", &val)); // out of range
    assert(!safe_strtoull(" issue221", &val));  // non-numeric

    // extremes:
    assert(safe_strtoull("18446744073709551615", &val)); // 2**64 - 1
    assert(val == 18446744073709551615ULL);
    assert(!safe_strtoull("18446744073709551616", &val)); // 2**64
    assert(!safe_strtoull("-1", &val));  // negative

    // huge number, with a negative sign _past_ the value
    assert(safe_strtoull("18446744073709551615\r\nextrastring-morestring", &val));
    return TEST_PASS;
}
*/


//what about
//assert(safe_strtoull("123 999", &val));
//assert(val == 123);
//assert(safe_strtoull("123\n999", &val));
//assert(val == 123);
//make assertions about errno value

//write down a concrete list of possible experiments, 
//ending with investigating a property with the broadest possible input values

// in a very expanded experiment, should i also add _meta_flag_preparse and other methods that use safe_strtoull in the harness?
// -> Dont do that! waste of time and no grade improvement

//uses of safe_strtoull in memcached:
//proxy_internal.c/process_update_cmd
//proxy_internal.c/process_arithmetic_cmd
//proxy_internal.c/_meta_flag_preparse
//testapp.c/test_safe_strtoull
//proto_text.c/_meta_flag_preparse
//proto_text.c/process_update_command
//proto_text.c/process_arithmetic_command
//memcached.c/do_add_delta
//memcached.c/_mc_meta_load_cb (in various different switch cases)

//_meta_flag_preparse,process_arithmetic_cmd and process_update_cmd are reused 
//in both proxy_internal.c and proto_text.c see if theyre actually identical


//pr created in proto_proxy.c/proxy_process_command ?
//pr stems from &rq in proxy_request.c/mcp_request_render and mcp_parser_t in mcplib_request ?
//and rq stems from luaL_checkudata() which is a method from an outside library?

//delta, initial and req_cas_id can all be taken from the proxy_internal.c/_meta_flags object instance (but arent always, watch out)


//running pure ./esbmc safe_strtoull_harness.c
// -> infinite safe_strtoull_harness.c line 167 loop
//ESBMC doesnt understand errno or strtoull?
//WARNING: no body for function __errno_location
//WARNING: no body for function strtoull
//WARNING: no body for function __errno_location


//Potential properties:

//no-data-race:
// ./esbmc --no-div-by-zero-check --force-malloc-success --state-hashing --add-symex-value-sets --no-align-check --k-step 2 --floatbv --unlimited-k-steps --no-vla-size-check "/home/erdnakram/Documents/Memcached Clone/memcached github git clone/memcached/safe_strtoull_harness.c" --64 --witness-output witness.graphml --no-pointer-check --no-bounds-check --data-races-check --no-assertions --k-induction --max-inductive-step 3 
// Segmentation fault (core dumped), doesnt make sense to test here


//no-overflow.prp:
// ./esbmc --no-div-by-zero-check --force-malloc-success --state-hashing --add-symex-value-sets --no-align-check --k-step 2 --floatbv --unlimited-k-steps --no-vla-size-check "/home/erdnakram/Documents/Memcached Clone/memcached github git clone/memcached/safe_strtoull_harness.c" --64 --witness-output witness.graphml --no-pointer-check --no-bounds-check --overflow-check --no-assertions --k-induction --max-inductive-step 3
// Infinite loop unwinding, check again later
// presumedly because string.c isnt limited, how do i limit a function that i dont even directly call?
// also what is line 319 in string.c

//termination.prp:
// ./esbmc --no-div-by-zero-check --force-malloc-success --state-hashing --add-symex-value-sets --no-align-check --k-step 2 --floatbv --unlimited-k-steps --no-vla-size-check "/home/erdnakram/Documents/Memcached Clone/memcached github git clone/memcached/safe_strtoull_harness.c" --64 --witness-output witness.graphml --no-pointer-check --no-bounds-check --no-assertions --termination --max-inductive-step 3 
// Infinite loop unwinding, check again later
// presumedly because string.c isnt limited, how do i limit a function that i dont even directly call?
// also what is line 319 in string.c

//unreach-call.prp:
// ./esbmc --no-div-by-zero-check --force-malloc-success --state-hashing --add-symex-value-sets --no-align-check --k-step 2 --floatbv --unlimited-k-steps --no-vla-size-check "/home/erdnakram/Documents/Memcached Clone/memcached github git clone/memcached/safe_strtoull_harness.c" --64 --witness-output witness.graphml --enable-unreachability-intrinsic --no-pointer-check --interval-analysis --no-bounds-check --error-label ERROR --goto-unwind --unlimited-goto-unwind --k-induction --max-inductive-step 3 
// verification successful (up to the nondet variable limit i set) -> because i made no assertions that could be false!!!

//valid-memcleanup.prp:
// ./esbmc --no-div-by-zero-check --force-malloc-success --state-hashing --add-symex-value-sets --no-align-check --k-step 2 --floatbv --unlimited-k-steps --no-vla-size-check "/home/erdnakram/Documents/Memcached Clone/memcached github git clone/memcached/safe_strtoull_harness.c" --64 --witness-output witness.graphml --no-pointer-check --no-bounds-check --memory-leak-check --no-assertions --incremental-bmc 
// Infinite loop unwinding, check again later
// presumedly because string.c isnt limited, how do i limit a function that i dont even directly call?
// also what is line 319 in string.c

//valid-memsafety.prp:
// ./esbmc --no-div-by-zero-check --force-malloc-success --state-hashing --add-symex-value-sets --no-align-check --k-step 2 --floatbv --unlimited-k-steps --no-vla-size-check "/home/erdnakram/Documents/Memcached Clone/memcached github git clone/memcached/safe_strtoull_harness.c" --64 --witness-output witness.graphml --memory-leak-check --no-reachable-memory-leak --no-assertions --no-abnormal-memory-leak --malloc-zero-is-null --incremental-bmc 
// Counterexample found at line 23: errno = 0; so presumedly just because it doesnt know what errno is, fix that


//maybe if i implement strtoull (or even __errno_location) the termination problem goes away?
//or maybe the problem is actually with safe_strtoull_harness.c line 166



//before fully implementing strtoull() reference back to your workflow. start by not implementing -> nondeterministic result -> then very simplified version -> then version without extra safety checks etc -> then full version (what else am i missing)

//Implementing errno:
//remember to explain why i have to implement and why the error esbmc returned isnt possible (for which you need to make certain you understand the esbmc commands and nondet properly!!!)

//errno is declared in errno.h, under 
extern int *__errno_location (void) __THROW __attribute_const__;
#define errno (*__errno_location())
//errno #define(s) are along this path of #include packages:
//include/errno.h -> bits/errno.h -> linux/errno.h -> asm/errno.h -> asm-generic/errno.h (cases 35-133)-> errno-base.h (cases 1-34)
//the one we care about is ERANGE, which is under errno-base.h as: 
#define	ERANGE		34	/* Math result not representable */

//include/errno.h -> features.h -> sys/cdefs.h defines __THROW and __attribute_const__
//maybe just ask what __attribute__ and __const__ in cdefs.h are and how errno generally works. or just ignore it

//but start by just removing it entirely (or setting it =0)
//still should understand how errno works, at what point is it called and the value potentially set to 34?
//i guess the term definitions are set at compile time, 
//and then at runtime *__errno_location() executes to check for potential overflows and returns 34 if there is one?

// so this:
//(errno == ERANGE)
// is equivalent to this:
//(*__errno_location() == 34)
//Basically just imagine it as equivalent to a throw in Java where the system magically has some predefined throws

//Thomas guess was: ESBMC doesnt recognise __errno_location(), so it assumes the adresse value can also be 0, 
//but seeing that we use __errno_location() as a pointer with *, that means we could have a pointer to adresse 0, 
//which would be invalid, hence why it returns an error when it shouldnt 
//(not to be confused with the value of the errno being =0; i mean the adresse where the value is located could 
//theoretically be 0 if the method is undefined -> adresse is nondet, and if that adresse is =0 we have an invalid adresse 
//-> error (when there shouldnt be one))

//his solution: pre-process, sodass __errno_location() mit in den dfinitionen ist
//-> see file test_errno.c and test_errno.i



