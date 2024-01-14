#include <stdlib.h>//for size_t and abort()
#include <stdio.h>
#include <string.h>//for memset
#include <stdint.h>//for uintX_t types
#include <assert.h>


#define POWER_SMALLEST 1
//#define POWER_LARGEST  256 /* actual cap is 255 */
//#define SLAB_GLOBAL_PAGE_POOL 0 /* magic slab class for storing pages for reassignment */
#define CHUNK_ALIGN_BYTES 8
/* slab class max is a 6-bit number, -1. */
#define MAX_NUMBER_OF_SLAB_CLASSES (63 + 1)

//implicit declarations:
//extern unsigned int __VERIFIER_nondet_uint();
//extern int __VERIFIER_nondet_int();
//extern size_t __VERIFIER_nondet_size_t();

struct settings{
    double factor;            /*chunk size growth factor*/
    int item_size_max;        /* Maximum item size */
    int chunk_size;
    int slab_chunk_size_max;  /* Upper end for chunks within slab pages. */
    int slab_page_size;       /* Slab's page units. */
};

/*extern*/ struct settings settings; //or: struct settings settings = {1024*1024};

typedef struct {
    unsigned int size;      /* sizes of items */
} slabclass_t;

static slabclass_t slabclass[MAX_NUMBER_OF_SLAB_CLASSES];

static int power_largest;

typedef struct _stritem {
    /* Protected by LRU locks */
    struct _stritem *next;                                                          //assuming these adresse pointers can be =NULL?
    struct _stritem *prev;                                                          //assuming these adresse pointers can be =NULL?
    /* Rest are protected by an item lock */
    struct _stritem *h_next;    /* hash chain next */                               //assuming these adresse pointers can be =NULL?
    unsigned int      time;       /* least recent access */                         //rel_time_t==unsigned int type -> size=4
    unsigned int      exptime;    /* expire time */                                 //rel_time_t==unsigned int type -> size=4
    int             nbytes;     /* size of data */                                  //-> size=4
    unsigned short  refcount;                                                       //-> size=2
    uint16_t        it_flags;   /* ITEM_* above */                                  //-> size=2
    uint8_t         slabs_clsid;/* which slab class we're in */                     //-> size=1
    uint8_t         nkey;       /* key length, w/terminating null and padding */    //-> size=1
    /* this odd type prevents type-punning issues when we do
     * the little shuffle to save space when not using CAS. */
    union {
        uint64_t cas;                                                               //-> size=8
        char end;                                                                   //-> size=1
    } data[];
    /* if it_flags & ITEM_CAS we have 8 bytes CAS */
    /* then null-terminated key */
    /* then " flags length\r\n" (no terminating null) */
    /* then data with terminating \r\n (no terminating null; it's binary!) */
} item;

//void slabs_init(/*const size_t limit,*/ const double factor,/* const bool prealloc,*/ const uint32_t *slab_sizes/*, void *mem_base_external, bool reuse_mem*/) {
void slabs_init(const double factor, const uint32_t *slab_sizes) {
    int i = POWER_SMALLEST - 1;
    unsigned int size = sizeof(item) + settings.chunk_size;//adapt my modelling of settings to include chunk_size=48;
    //unsigned int lastsize = 0;
    memset(slabclass, 0, sizeof(slabclass));

    while (++i < MAX_NUMBER_OF_SLAB_CLASSES-1) {
        //if(size*factor<=size){abort();}// for some reason this doesnt prevent the erroneous false_reach. SO i guess it seems like size is just reset at the end of every loop
        //lastsize=size;
        //if (slab_sizes != NULL) {
        //    if (slab_sizes[i-1] == 0){}
        //        break;
        //    }
        //    size = slab_sizes[i-1];
        //} else if (size >= settings.slab_chunk_size_max / factor) {
        if (size >= settings.slab_chunk_size_max / factor) {
        //if size >= the second to last chunk size/slab class? what about the slab class where an item take up a while slab page. re-read my notes again
            break;
        }
        /* Make sure items are always n-byte aligned */
        if (size % CHUNK_ALIGN_BYTES){
            size += CHUNK_ALIGN_BYTES - (size % CHUNK_ALIGN_BYTES);
        }

        slabclass[i].size = size;

        if (slab_sizes == NULL){
            size *= factor;
        }
        //if(!(size > 96)){abort();} //if this is included, then our assertion that should always be correct, is. Still dont understand why it would ever be false though
        //if(size==lastsize){abort();}//also works

    }//due to i incrementing before setting slabclass[i], we start initialising values at slabclass[1].size = size; , not slabclass[0].size = size;
    //so because of this and memset(slabclass, 0, sizeof(slabclass)); , slabclass[0].size is set =0 (not considering the slab_sizes != NULl case)

    //example of loop run, starting at where were already in the loop at the end of i=4:
    //we set slabclass[4].size = size; , do size*=factor and increment to i=5, now size >= settings.slab_chunk_size_max/factor, 
    //meaning with i=6 we would have had size >= settings.slab_chunk_size_max. 
    //instead we break at i=5 , set power_largest=5 and slabclass[5].size = settings.slab_chunk_size_max;

    //example where break is reached: (ignoring byte align)
    //slab_chunk_size_max=75 -> settings.slab_chunk_size_max / factor=60 ; and starting chunk size=40
    //class[1]=40 -> size*=factor=50 -> increment i=2 -> 50<60 -> class[2]=50 -> size*=factor=62.5 -> increment i=3 -> 62.5>=60 -> power_largest=3 -> class[3]=75

    //why is the if(size >= settings.slab_chunk_size_max / factor) clause not if(size >= settings.slab_chunk_size_max). wouldnt that make a lot more sense?
    //class[1]=40 -> size*=factor=50 -> increment i=2 -> 50<60 -> class[2]=50 -> size*=factor=62.5 -> increment i=3 -> 62.5<70 -> class[3]=62.5 -> size*=factor=78
    //-> increment i=4 -> 78>=75 -> power_largest=4 -> class[3]=75

    //either way, point is, the last class is set to size=slab_chunk_size_max, an item greater than that would have to take up a whole slab page, i think?
    //another oddity i touched on here before, irrelevant of whether item size in slabs_clsid is =70 or =80, in these examples slab class=3 would be returned 
    //either way, even though one option would fit, but the other wouldnt

    power_largest = i;
    slabclass[power_largest].size = settings.slab_chunk_size_max;
}//later make an assertion whether power_largest = 63 (leaving the while loop naturally) is ever even reachable if slab_sizes==NULL
//cause right now we have 48*1.25^62=48939783.5 for size by the end of the loop (if you removed the break option) (not account for rounding size up each loop)
//vs (1024*1024/2)/1.25=419430.4 for the loop break condition
//even if page size limit were increased to 1GB -> (1024*1024*1024/2)/1.25, it still wouldnt be large enough


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
}//if size is so small that its less than slabclass[1].size, we immediately return that it fits in slab class 1 without going into the while loop
//


int main(){

//Encode Precondition (Arrange):
    //size_t input_item_size = __VERIFIER_nondet_size_t();//(just do broad nondet or fixed value for now)
    size_t input_item_size = 2028;
    
    settings.factor = 1.25;//set to default value; //1 //1.01 //1.1 //5 //1000
    //another thing to consider is if factor is small enough it will never get past the CHUNK_ALIGN_BYTES rounding and be [0,96,96,...,96,524288], which could lead to issues
    settings.item_size_max = 1024 * 1024;//set to default value; 
    settings.chunk_size = 48;//set to default value; 
    settings.slab_page_size = 1024 * 1024; /* chunks are split from 1MB pages. */
    settings.slab_chunk_size_max = settings.slab_page_size / 2;
    //maybe make a limitation that item_size_max<=slab_page_size if needed
    //or better yet leave it out, then, if theres a related error, verify in memcached whether the intended rule actually always applies
    //due to the combination of catches at memcached.c#5758 and beyond we know:
    //item_size_max >= slab_chunk_size_max
    //slab_page_size >= slab_chunk_size_max (otherwise slab_page_size % slab_chunk_size_max == 0 couldnt be true)
    
	//slabclass[MAX_NUMBER_OF_SLAB_CLASSES-1].size = 0;//maybe set this later

//Main Verification Harness:
    slabs_init(settings.factor,NULL);
    //power_largest still goes from 1-63 (as can be seen in slabs_init, and limited by slabclass[] index range)
    //as all our values are fixed we can actually know exactly what our slabclasses are:
    //...
    unsigned int out = slabs_clsid(input_item_size);

    printf("[");
    unsigned int i;
    for(i = 0; i < MAX_NUMBER_OF_SLAB_CLASSES-1; i++) {
		//printf("%d, ",slabclass[i].size);
        printf("'index;%d, value:%d', ",i,slabclass[i].size);
	}
    //printf("%d]\n",slabclass[i].size);
    printf("'index;%d, value:%d']\n, ",i,slabclass[i].size);
    //slabclass[0].size = 48+48
    printf("%d\n",settings.slab_chunk_size_max);

//Encode Postcondition (Assert):
    //...
    assert(slabclass[39].size == settings.slab_chunk_size_max);//should always be true, but ESBMC seems to think that factor=1 and size=96 is always set
    return 1;
}