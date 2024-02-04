#include <stdlib.h>//for size_t and abort()
#include <stdio.h>
#include <string.h>//for memset
#include <stdint.h>//for uintX_t types
#include <assert.h>
#include <stdbool.h>//for boolean values

#define ITEM_SIZE_MAX_LOWER_LIMIT 1024
#define ITEM_SIZE_MAX_UPPER_LIMIT 1024 * 1024 * 1024 
#define POWER_SMALLEST 1
#define CHUNK_ALIGN_BYTES 8
#define MAX_NUMBER_OF_SLAB_CLASSES (63 + 1)

//implicit declarations:
//... [__VERIFIER_nondet_X declarations]

static slabclass_t slabclass[MAX_NUMBER_OF_SLAB_CLASSES];
static int power_largest;

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
           size <= last_size ||
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
    memset(slabclass, 0, sizeof(slabclass));//elements of slabclass initialized to zero
    while (++i < MAX_NUMBER_OF_SLAB_CLASSES-1) {
        if (slab_sizes_input != NULL) {
            if (slab_sizes_input[i-1] == 0){//end of slab_sizes_input reached
                break;
            }
            size = slab_sizes_input[i-1];
        } else if (size >= settings.slab_chunk_size_max / factor) {
            break;
        }
        if (size % CHUNK_ALIGN_BYTES){/* Make sure items are always n-byte aligned */
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
        if (res++ == power_largest)
            //1<=power_largest<=63
            return power_largest;
    return res;
}

int main(){

//Encode Precondition (Arrange):
    size_t input_item_size = __VERIFIER_nondet_size_t();/
    settings.maxbytes = 64 * 1024 * 1024; /* default is 64MB */
    unsigned int factor_convert = __VERIFIER_nondet_uint();
    if(factor_convert <= 100 || factor_convert > 4294967200){abort();}//-> between 1 and 42949672
    settings.factor = (double)factor_convert/100.0;//-> converted double with 2 values after decimal point
    //settings.factor = __VERIFIER_nondet_double();
    settings.item_size_max = __VERIFIER_nondet_int();
    if (settings.item_size_max < ITEM_SIZE_MAX_LOWER_LIMIT ||//            1024
        settings.item_size_max > ITEM_SIZE_MAX_UPPER_LIMIT ||//1024^3    = 1.073.741.824
        settings.item_size_max > (settings.maxbytes / 2))  { //32*1024^2 = 33.554.432
        abort();
    }
    settings.chunk_size = __VERIFIER_nondet_int();
    if(settings.chunk_size <= 0 || settings.chunk_size > 300){abort();}    
    settings.slab_page_size = 1024 * 1024; /* chunks are split from 1MB pages. */
    bool slab_chunk_max_opt_used = __VERIFIER_nondet_bool();
    bool no_chunked_items_opt_used = __VERIFIER_nondet_bool();
    bool slab_chunk_size_changed = false;
    settings.slab_chunk_size_max = settings.slab_page_size / 2;
    //potential case SLAB_CHUNK_MAX:
    if(slab_chunk_max_opt_used){
        settings.slab_chunk_size_max = __VERIFIER_nondet_int();
        bool slab_chunk_size_changed = true;
    }
    //potential case NO_CHUNKED_ITEMS:
    if (no_chunked_items_opt_used) {
        settings.slab_chunk_size_max = settings.slab_page_size;
    }
    //safety checks:
    if (settings.item_size_max > 1024 * 1024 && !slab_chunk_size_changed) {
        settings.slab_chunk_size_max = settings.slab_page_size/2;
    }
    if (settings.slab_chunk_size_max > settings.item_size_max ||
        settings.item_size_max % settings.slab_chunk_size_max != 0 ||
        settings.slab_page_size % settings.slab_chunk_size_max != 0)
        {
        abort();
    }
    bool use_slab_sizes = __VERIFIER_nondet_bool();

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
    //... [various assertions]
    return 1;
}