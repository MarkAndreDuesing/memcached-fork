#include <stdlib.h>//for size_t and abort()
#include <stdio.h>
#include <string.h>//for memset
#include <stdint.h>//for uintX_t types
#include <assert.h>
#include <stdbool.h>//for boolean values
#include <limits.h>

#define ITEM_SIZE_MAX_LOWER_LIMIT 1024
#define ITEM_SIZE_MAX_UPPER_LIMIT 1024 * 1024 * 1024 
#define POWER_SMALLEST 1
#define CHUNK_ALIGN_BYTES 8
/* slab class max is a 6-bit number, -1. */
#define MAX_NUMBER_OF_SLAB_CLASSES (63 + 1)

//implicit declarations:
extern unsigned int __VERIFIER_nondet_uint();
extern int __VERIFIER_nondet_int();
extern size_t __VERIFIER_nondet_size_t();
extern _Bool __VERIFIER_nondet_bool();
extern double __VERIFIER_nondet_double();

struct settings{
    double factor;            /*chunk size growth factor*/
    int item_size_max;        /* Maximum item size */
    int chunk_size;
    int slab_chunk_size_max;  /* Upper end for chunks within slab pages. */
    int slab_page_size;       /* Slab's page units. */
    size_t maxbytes;
} settings;

typedef struct {
    unsigned int size;      /* sizes of items */
} slabclass_t;

static slabclass_t slabclass[MAX_NUMBER_OF_SLAB_CLASSES];

static int power_largest;


typedef struct _stritem {
    struct _stritem *next;
    struct _stritem *prev;
    struct _stritem *h_next;    /* hash chain next */
    unsigned int      time;     /* least recent access */
    unsigned int      exptime;  /* expire time */
    int             nbytes;     /* size of data */
    unsigned short  refcount;
    uint16_t        it_flags;   /* ITEM_* above */
    uint8_t         slabs_clsid;/* which slab class we're in */
    uint8_t         nkey;       /* key length, w/terminating null and padding */
    union {
        uint64_t cas;
        char end;
    } data[];
} item;



void _parse_slab_sizes(uint32_t *slab_sizes) {
    uint32_t size = 0;
    uint32_t last_size = 0;
    int i = 0;

    for (i = 0; i < MAX_NUMBER_OF_SLAB_CLASSES-2; i++){

        size = (uint32_t) __VERIFIER_nondet_uint();
        
        if(size < settings.chunk_size ||
        size > settings.slab_chunk_size_max ||
        last_size >= size ||
        last_size<=UINT_MAX-8||//overflow experiment protection (remove later)
        size <= last_size + CHUNK_ALIGN_BYTES){ //false cases
            abort();
        } 
        slab_sizes[i] = size;
        last_size = size;
    }
    slab_sizes[i] = 0;
}


void slabs_init(const double factor, const uint32_t *slab_sizes_input) {
    int i = POWER_SMALLEST - 1;
    unsigned int size = sizeof(item) + settings.chunk_size;
    memset(slabclass, 0, sizeof(slabclass));
    while (++i < MAX_NUMBER_OF_SLAB_CLASSES-1) {
        if (slab_sizes_input != NULL) {
            if (slab_sizes_input[i-1] == 0){
                break;
            }
            size = slab_sizes_input[i-1];
        } else if (size >= settings.slab_chunk_size_max / factor) {
            break;
        }
        /* Make sure items are always n-byte aligned */
        if (size % CHUNK_ALIGN_BYTES){
            size += CHUNK_ALIGN_BYTES - (size % CHUNK_ALIGN_BYTES);
        }
        slabclass[i].size = size;
        if (slab_sizes_input == NULL){
            size *= factor;
        }
    }
    power_largest = i;
    slabclass[power_largest].size = settings.slab_chunk_size_max;
}

unsigned int slabs_clsid(const size_t size) {
    int res = POWER_SMALLEST;

    if (size == 0 || size > settings.item_size_max)
        return 0;
    while (size > slabclass[res].size)
        if (res++ == power_largest)//1<=power_largest<=63
            return power_largest;
    return res;
}

int main(){

//Encode Precondition (Arrange):
    size_t input_item_size = __VERIFIER_nondet_size_t();//(just do broad nondet or fixed value for now)
    //if(input_item_size<sizeof(item)){abort();} //could add

    settings.maxbytes = 64 * 1024 * 1024; /* default is 64MB */
    settings.slab_page_size = 1024 * 1024; /* chunks are split from 1MB pages. */

    int factor_convert = __VERIFIER_nondet_int();
    if(factor_convert <= 100 || factor_convert > 1000000){abort();}
    //-> between 1 and 10000 (could also use > 4294967200 at the most -> f=42949672 max)
    //int factor_convert = 125;
    settings.factor = (double)factor_convert/100.0;//-> converted double with 2 values after decimal point

    settings.item_size_max = __VERIFIER_nondet_int();/* default is 1024*1024 */
    if (settings.item_size_max < ITEM_SIZE_MAX_LOWER_LIMIT ||//            1024
        settings.item_size_max > ITEM_SIZE_MAX_UPPER_LIMIT ||//1024^3    = 1.073.741.824
        settings.item_size_max > (settings.maxbytes / 2))  { //32*1024^2 = 33.554.432 
        //at the very lowest maxbytes can be 8*1024*1024, according to proto_text.c . But i seem to be able to set it to 1*1024*1024 (but no lower) 
        //-> would result in a single page being created?
        abort();
    }

    settings.chunk_size = __VERIFIER_nondet_int();/* default is 48 */
    if(settings.chunk_size == 0){abort();}
    //if(settings.chunk_size <= 0 || settings.chunk_size > 300){abort();} //added for experiments (remove later)

//    bool slab_chunk_max_opt_used = __VERIFIER_nondet_bool();
//    bool no_chunked_items_opt_used = __VERIFIER_nondet_bool();
//    bool no_modern_opt_used = __VERIFIER_nondet_bool();
//    bool slab_chunk_size_changed = false;

//    settings.slab_chunk_size_max = settings.slab_page_size / 2;//default value, which can potentially be overwritten
      //also removed, as this slab_page_size/2 value can also just occur through __VERIFIER_nondet_int();

//potential case SLAB_CHUNK_MAX:
//    if(slab_chunk_max_opt_used){
        settings.slab_chunk_size_max = __VERIFIER_nondet_int();
        //if(settings.slab_chunk_size_max < settings.chunk_size){abort();}//added for experiments (remove later)
        //bool slab_chunk_size_changed = true;
//    }

//cases removed for redundancy:
//potential case NO_CHUNKED_ITEMS:
//    if (no_chunked_items_opt_used) {
//        settings.slab_chunk_size_max = settings.slab_page_size;
//    }
//potential case NO_MODERN:
//    if (no_modern_opt_used && !slab_chunk_size_changed) {
//        settings.slab_chunk_size_max = settings.slab_page_size;
//    }


//safety checks:

//    if (settings.item_size_max > 1024 * 1024 && !slab_chunk_size_changed) {
//        settings.slab_chunk_size_max = settings.slab_page_size/2;
//    }//case removed for redundancy

    if (settings.slab_chunk_size_max > settings.item_size_max ||
        settings.item_size_max % settings.slab_chunk_size_max != 0 ||//items divisible by max chunk size
        //due to this slab_chunk_size_max can also not be < -(item_size_max) even on underflow
        settings.slab_page_size % settings.slab_chunk_size_max != 0)//pages divisible by max chunk size
        //This clause prevents slab_chunk_size_max > slab_page_size, and as slab_page_size cannot be changed, never greater than 1024^2. 
        //Due to this slab_chunk_size_max also has to come in powers of 2, e.g. 2^x
        //due to this slab_chunk_size_max can also not be < -(slab_page_size) even on underflow
        {
        abort();
        //Im pretty sure these safety cases can also lead to "Floating point exception (core dumped)" if slab_chunk_size_max=0. Investigate further
    }
    //maybe make a limitation that item_size_max<=slab_page_size if needed
    

//Main Verification Harness:
    if(use_slab_sizes){
        uint32_t slab_sizes[MAX_NUMBER_OF_SLAB_CLASSES];
        _parse_slab_sizes(slab_sizes);
        slabs_init(settings.factor,slab_sizes);
    } else {
        slabs_init(settings.factor,NULL);
    }
    unsigned int out = slabs_clsid(input_item_size);

//Encode Postcondition (Assert):

    

    

    //maybe try to fit this assertion in somewhere after slab class increasing size assertion!:
    //unsigned int item_size = sizeof(item);
    //bool any_greater = false;
    //for (int i = 0; i <= power_largest-1; i++){
    //    if (slabclass[i].size>item_size) {
    //        any_greater = true;
    //    }
    //}
    //assert(any_greater);//should be unreachable, as some slab class from 0 to power_largest-1 should be able to hold the empty item

    return 1;
}

/*
assertions/investigations:

start with: 

[1.5h]
power_largest and res array bound tests, which will most likely turn out safe
z.B.
    //array bound error cannot occur example assertion:
    //assert(power_largest<=MAX_NUMBER_OF_SLAB_CLASSES-1);//proven correct!
    //2) assert if theres any way for power_largest to be =0 -> res would iterate repeatedly into an array bound error:
    //-> assert(1<=power_largest);
    //assert(out>=0 && out<=power_largest);

[1h]
safety case assertions:
z.B.
    //if (size != 0 && size <= settings.item_size_max){assert(res!=0);}
and
1) 0 could be returned in unwanted circumstances, depending on factors such as changing \verb|item_size_max| ->
Equivalence assertion (item size<=0 or greater than max item size <==> res = 0)
See if couterexamples either direction

[6h]
Then continuation on 48+(-10) error -> all slab sizes 0 -> perslab addition

(counterexample to "each slab class bigger than the last")
Make assertion class0 to n-2 same
Then class0 to n-1 same 
Then class0 to n-1 same and >0
z.B.

    //slabclass[i+1]>slabclass[i]
    //make assert that every slab class bigger than the last, then invert to see if ESBMC can find example

    //and that slabclass[power_largest] is biggest in array
    
    //for (int i = 0; i <= power_largest-2; i++){//can also try power_largest-1 to include slabclass[power_largest].size
    //    assert(slabclass[i+1].size>slabclass[i].size);
    //    assert(slabclass[i+1].size>=slabclass[i].size);
    //}

(find various ways this can be achieved including steering ESBMC towards the very small factor possibility -> "very small factor (1.001) unable to overcome n-byte alignment")
-> results in something like "memcached -n 8 -f 1.01 -o slab_chunk_max=64 -vv" leads to !=0 slab classes all identical, while still actually being resonable! (steer in that direction)
using stats slabs you can then see that only slab 1 and slab 63 are ever used, none of the others!
-> leads to segmentation fault, but i only kinda understand why, probably wont have time to figure out

[1.5h]
Show memcached -... float point expection core dumped (based on a previous assertion counterexample) ->
Perslab calulation division probably causes floating point exception
-> remove --no-division-by-zero -> add perslab to moddeling

also remember slab_chunk_size_max=0 probably directly causes a core dump because of the safety check modulo% cases

[1.5h]
Also attempt at finding factor multiplication overflow
-> try to get esbmc to find the counterexaple where factor + the n-byte alignment can cause an overflow

Total 11.5h !!! no time to waste tomorrow!!!
-------------------------------------------------------
Other notes: 

remember not to overdo it, just do enough assertions to call it tested 
(add the memcached -... code lines for fun, but not enough to make a github issue over unless you get a runtime error and understand it fully!) 
(maybe check again that you covered the ones mentioned previously), then just fix the formatting 
(especially seperating experiments more; listings at top of page; chicago style experiment headers; check line width)

maybe also logically seperate into memory safety based assertions and overflow based assertions

later:
logically limit the variables to see if assertion errors can still occur z.b. chunk_size <= slab_chunk_size_max
(potentially remove the safety case or incorporate it into the harness)

another thing to look into: slab_chunk_size_max has to be smaller than item_size_max. But this doesnt account for the fact that slab_chunk_size_max and item_size_max are int, 
whereas size in _parse... and slabs_init is unsigned int. meaning you cheat this rule, alongwith many other errors
(probably wont have time for this in detail, leave to the end!)
*/