#include <stdlib.h>//for size_t and abort()
#include <stdio.h>
#include <string.h>//for memset


#define POWER_SMALLEST 1
//#define POWER_LARGEST  256 /* actual cap is 255 */
//#define SLAB_GLOBAL_PAGE_POOL 0 /* magic slab class for storing pages for reassignment */
//#define CHUNK_ALIGN_BYTES 8
/* slab class max is a 6-bit number, -1. */
#define MAX_NUMBER_OF_SLAB_CLASSES (63 + 1)

//implicit declarations:
extern unsigned int __VERIFIER_nondet_uint();
extern int __VERIFIER_nondet_int();
extern size_t __VERIFIER_nondet_size_t();

struct settings{
    int item_size_max;        /* Maximum item size */
};

/*extern*/ struct settings settings; //or: struct settings settings = {1024*1024};

typedef struct {
    unsigned int size;      /* sizes of items */
} slabclass_t;

static slabclass_t slabclass[MAX_NUMBER_OF_SLAB_CLASSES];

static int power_largest;


unsigned int slabs_clsid(const size_t size) {
    int res = POWER_SMALLEST;

    if (size == 0 || size > settings.item_size_max)
        return 0;
    while (size > slabclass[res].size)
        if (res++ == power_largest)
    //assuming power_largest=63 and res incremented to the point of res=62:
    //res:62==power_largest:63 false-> res incremented to:63 -> 63==63 true -> res incremented to:64 (but irrelevant as...) -> return power_largest=63
            return power_largest;
    return res;
}


int main(){

//Encode Precondition (Arrange):
    size_t input_item_size = __VERIFIER_nondet_size_t();//(just do broad nondet or fixed value for now)

    settings.item_size_max = 1024 * 1024;//set to default value; 
    
    //memset(slabclass, 0, sizeof(slabclass));
    for(unsigned int i = 0; i < MAX_NUMBER_OF_SLAB_CLASSES; i++) {//0-63 range
		slabclass[i].size = __VERIFIER_nondet_uint(); //initialise with nondet or fixed values for now (properly with slabs_init later) 
        //(will it still be static memory allocation later? check again)
	}//have to set --unwind to a value greater than 64 to avoid erroneous errors from the BMC loop unwinding
	//slabclass[MAX_NUMBER_OF_SLAB_CLASSES-1].size = 0;//maybe set this later

    power_largest = __VERIFIER_nondet_int();//move to harness (properly with slabs_init later) power_largest goes from 1-63 (as can be seen in slabs_init, 
    //but also logical here, as res is only supposed to go from 1-63, limited by slabclass[] index range)
    if(power_largest > MAX_NUMBER_OF_SLAB_CLASSES-1 || power_largest < POWER_SMALLEST) {abort();}

//Main Verification Harness:

    unsigned int out = slabs_clsid(input_item_size);

//Encode Postcondition (Assert):
    //...
    return 1;
}