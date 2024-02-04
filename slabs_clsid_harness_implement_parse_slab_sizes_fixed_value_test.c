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
} settings;

///*extern*/ struct settings settings; //or: struct settings settings = {1024*1024};

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


void _parse_slab_sizes(uint32_t *slab_sizes) {
    uint32_t size = 0;
    uint32_t last_size = 0;
    int i = 0;

    for (i = 0; i < MAX_NUMBER_OF_SLAB_CLASSES-2; i++){

        //size = (uint32_t) __VERIFIER_nondet_uint();
        
        //fixed inputs tests:
        //size = last_size+10000;
        //size = last_size+48;
        size = last_size+13500;

        if(size < settings.chunk_size ||
        size > settings.slab_chunk_size_max ||
        last_size >= size ||
        size <= last_size + CHUNK_ALIGN_BYTES){ //false cases
            //abort();
            //for fixed inputs:
            printf("error"); break;
        } 
        slab_sizes[i] = size; //dont need to do i++, as we already increment at the end of every loop, and moved the upper limit safety check to the front of the loop
        last_size = size;
    }

    slab_sizes[i] = 0;
}


void slabs_init(const double factor, const uint32_t *slab_sizes) {
    int i = POWER_SMALLEST - 1;
    unsigned int size = sizeof(item) + settings.chunk_size;//adapt my modelling of settings to include chunk_size=48;
    unsigned int lastsize = 0;
    memset(slabclass, 0, sizeof(slabclass));//-> all elements of the slabclass array have their size field initialized to zero.

    while (++i < MAX_NUMBER_OF_SLAB_CLASSES-1) {
        if (slab_sizes != NULL) {
            if (slab_sizes[i-1] == 0){
                break;
            }
            size = slab_sizes[i-1];
        } else if (size >= settings.slab_chunk_size_max / factor) {
        //if size >= the second to last chunk size/slab class? what about the slab class where an item take up a while slab page. re-read my notes again
            break;
        }
        /* Make sure items are always n-byte aligned */
        if (size % CHUNK_ALIGN_BYTES){
            size += CHUNK_ALIGN_BYTES - (size % CHUNK_ALIGN_BYTES);
        }
        slabclass[i].size = size;
        if (slab_sizes == NULL){
            lastsize = size;
            size *= factor;
            if(size==lastsize){abort();}//might have to add this catch if assertion tests still have the problem that factor multiplication is ignored
        }

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


//analyse: slabclass[res].size overflow due to factor
int main(){

//Encode Precondition (Arrange):
    //size_t input_item_size = __VERIFIER_nondet_size_t();//(just do broad nondet or fixed value for now)
    size_t input_item_size = 2028;
    
    settings.factor = 1.25;//set to default value; 
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

    //put nondet bool 'use_slab_sizes' around this later
    uint32_t slab_sizes[MAX_NUMBER_OF_SLAB_CLASSES];
    _parse_slab_sizes(slab_sizes);
    //and then do 'use_slab_sizes ? slab_sizes : NULL' in slabs_init

//Main Verification Harness:
    slabs_init(settings.factor,slab_sizes);
    
    //slabs_init(settings.factor,use_slab_sizes ? slab_sizes : NULL);
    
    //power_largest still goes from 1-63 (as can be seen in slabs_init, and limited by slabclass[] index range)
    //as all our values are fixed we can actually know exactly what our slabclasses are:
    //[0, 96, 120, 152, 192, 240, 304, 384, 480, 600, 752, 944, 1184, 1480, 1856, 2320, 2904, 3632, 4544, 5680, 7104, 8880, 11104, 13880, 17352, 21696, 27120, 33904, 
    //42384, 52984, 66232, 82792, 103496, 129376, 161720, 202152, 252696, 315872, 394840, 524288, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    //64 slab classes, 24 empty ones after slab_chunk_size_max cap reached. and as expected 394840*1.25 = 493550 which is < 524288, the slab_chunk_size_max value
    //so the odd class distribution is intentional
    //another factor here i didnt consider before is that if we accidentally returned res=power_largest+1, we would get the slab class size: slabclass[power_largest+1].size=0
    unsigned int out = slabs_clsid(input_item_size);

//Encode Postcondition (Assert):
    //...

    printf("[");
    unsigned int j;
    for(j = 0; j < MAX_NUMBER_OF_SLAB_CLASSES-1; j++) {
        printf("'index;%d, value:%d', ",j,slab_sizes[j]);
    }
    printf("'index;%d, value:%d']\n, ",j,slab_sizes[j]);


    printf("[");
    unsigned int k;
    for(k = 0; k < MAX_NUMBER_OF_SLAB_CLASSES-1; k++) {
        printf("'index;%d, value:%d', ",k,slabclass[k].size);
	}
    printf("'index;%d, value:%d']\n, ",k,slabclass[k].size);

printf("%d\n",settings.slab_chunk_size_max);

//as expected, converting from slab_sizes to slabclass.size, we add a 0 to the front (i=0) and slab_chunk_size_max to the back (i=63)
//with which the 2 free indices left by slab_sizes (i=62->0 and i=63->undef) are used up
//this still leaves the ==NULL oddly technically different to the !=NULL variant, but neither are technically faulty, just implemented differently


//assert(slab_sizes[MAX_NUMBER_OF_SLAB_CLASSES-3] != settings.slab_chunk_size_max);
//assert(slab_sizes[MAX_NUMBER_OF_SLAB_CLASSES-3] == settings.slab_chunk_size_max);
//assert(slab_sizes[MAX_NUMBER_OF_SLAB_CLASSES-2] != 0);
//-> found counterexample for all of these -> correct behaviour
//assert(slab_sizes[MAX_NUMBER_OF_SLAB_CLASSES-2] == 0);//should always be true, and it is according to esbmc -> correct behaviour




    return 1;
}