//slabs_init() definition:
//Only used once, set in main() with:
//slabs_init(settings.maxbytes, settings.factor, preallocate,use_slab_sizes ? slab_sizes : NULL, mem_base, reuse_mem);

//https://github.com/memcached/memcached/blob/490a4aa483e0073735d636c57ed5a7056e06ada3/doc/protocol.txt#L1439:
//Settings statistics
//The "stats" command with the argument of "settings" returns details of
//the settings of the running memcached.  This is primarily made up of
//the results of processing commandline options.
//maxbytes | size_t | Maximum number of bytes allowed in the cache

//https://github.com/memcached/memcached/blob/490a4aa483e0073735d636c57ed5a7056e06ada3/slabs.c#L682
//settings.maxbytes = new_mem_limit;


//item_size_max     | size_t   | maximum item size 
//slab_chunk_max    | 32       | Max slab class size (avoid unless necessary)



//#include "memcached.h"
//#include "storage.h"
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/resource.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <errno.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <signal.h>
#include <assert.h>
#include <pthread.h>


#define POWER_SMALLEST 1
#define MAX_NUMBER_OF_SLAB_CLASSES (63 + 1)
#define CHUNK_ALIGN_BYTES 8

typedef struct {
    unsigned int size;      /* sizes of items */
    //unsigned int perslab;   /* how many items per slab */

    void *slots;           /* list of item ptrs */
    unsigned int sl_curr;   /* total free items in list */

    unsigned int slabs;     /* how many slabs were allocated for this class */

    void **slab_list;       /* array of slab pointers */
    unsigned int list_size; /* size of prev array */
} slabclass_t;//not sure if i can actually just exclude the other fields because we use sizeof(slabclass), but try for now

static slabclass_t slabclass[MAX_NUMBER_OF_SLAB_CLASSES];

/**
 * Determines the chunk sizes and initializes the slab class descriptors
 * accordingly.
 */
/** Init the subsystem. 1st argument is the limit on no. of bytes to allocate,
    0 if no limit. 2nd argument is the growth factor; each slab will use a chunk
    size equal to the previous slab's chunk size times this factor.
    3rd argument specifies if the slab allocator should allocate all memory
    up front (if true), or allocate memory in chunks as it is needed (if false)
*/
void slabs_init(const size_t limit, const double factor, const bool prealloc, const uint32_t *slab_sizes, void *mem_base_external, bool reuse_mem) {
    int i = POWER_SMALLEST - 1;
    unsigned int size = sizeof(item) + settings.chunk_size;

    /* Some platforms use runtime transparent hugepages. If for any reason
     * the initial allocation fails, the required settings do not persist
     * for remaining allocations. As such it makes little sense to do slab
     * preallocation. */
    /*
    bool __attribute__ ((unused)) do_slab_prealloc = false;

    mem_limit = limit;

    if (prealloc && mem_base_external == NULL) {
        mem_base = alloc_large_chunk(mem_limit);
        if (mem_base) {
            do_slab_prealloc = true;
            mem_current = mem_base;
            mem_avail = mem_limit;
        } else {
            fprintf(stderr, "Warning: Failed to allocate requested memory in"
                    " one large chunk.\nWill allocate in smaller chunks\n");
        }
    } else if (prealloc && mem_base_external != NULL) {
        // Can't (yet) mix hugepages with mmap allocations, so separate the
        // logic from above. Reusable memory also force-preallocates memory
        // pages into the global pool, which requires turning mem_* variables.
        do_slab_prealloc = true;
        mem_base = mem_base_external;
        // _current shouldn't be used in this case, but we set it to where it
        // should be anyway.
        if (reuse_mem) {
            mem_current = ((char*)mem_base) + mem_limit;
            mem_avail = 0;
        } else {
            mem_current = mem_base;
            mem_avail = mem_limit;
        }
    }
    */
   //not relevant for our experiment as we only need to set slabclass[].size and power_largest

    memset(slabclass, 0, sizeof(slabclass));//global variable, maybe i need to keep all fields of slabclass for sizeof to be set correctly

    while (++i < MAX_NUMBER_OF_SLAB_CLASSES-1) {
        if (slab_sizes != NULL) {//slab_sizes given by slabs_init() input, which is defined in memcached.c:
        //uint32_t slab_sizes[MAX_NUMBER_OF_SLAB_CLASSES]; -> static array with maximum 64 elements and placements from slab_sizes[0] to slab_sizes[MAX_NUMBER_OF_SLAB_CLASSES-1]=slab_sizes[63]
        //slab_sizes can be NULL based on us bool use_slab_sizes is true or false.
        //It can be set to true in line https://github.com/memcached/memcached/blob/490a4aa483e0073735d636c57ed5a7056e06ada3/memcached.c#L5795 based on _parse_slab_sizes
        //From _parse_slab_sizes we cas assess that: 
        //a string is repeatedly split with strtok_r using the delimiter '-' (presumedly for each string split we do one loop. e.g. "123-123-123" will lead to 3 loops as we split into 3 parts)
        //safe_strtoul is used to read an unsigned long value into 'uint32_t size' from the split string. 
        //Then (after safety checks) size is used for slab_sizes[i++] = size; starting at slab_sizes[0]
        //safety case restrictions:
        //each size in slab_sizes[x] has to be size >= settings.chunk_size and size <= settings.slab_chunk_size_max
        //and last_size < size -> meaning that: slab size 'size' cannot be lower than or equal to a previous class size
        //and size > last_size + CHUNK_ALIGN_BYTES -> meaning that: slab size 'size' must be at least 'CHUNK_ALIGN_BYTES' bytes larger than previous class
        //and after incrementing 'i' ,we check if i==MAX_NUMBER_OF_SLAB_CLASSES-1 (=63). If it is then also return false
        //this is important as we set slab_sizes[i]=0; after the loop, so if slabs_sizes[63] is the highest element without going out of array bounds 
        //and we increment i after setting an element value, our highest element in the loop has to be slabs_sizes[62] (or less) so we can set slab_sizes[63]=0; (or less, depending on how many classes/string splits we actually needed -> how high our 'i' goes)
        //(which will probably be important for the if (slab_sizes[i-1] == 0) check in slabs_init() )
        
        //its probably best i dont go that in depth. maybe just make assumptions about slab_sizes, make an array with nondet values and move on, or just fixed values if you get difficult to interpret errors
        //say something along the lines of: "I wont go into further detail on _parse_slab_sizes beyond the information needed to set slab_sizes[], as this would go too far beyond the scope of the analysed method.
        //But we assume if _parse_slab_sizes returns true, slab_sizes[] was correctly initialised and use_slab_sizes is set to true. Then (slab_sizes != NULL) is also true.
        //From the internal functionality of _parse_slab_sizes we can make assumptions/restrictions on how slab_sizes[] is defined/generated. They are as follows..."
        //then in the harness use the nondet_bool idea i had to either set slab_sizes==NULL or set slab_sizes according to the restrictions/assumptions described
        //if i do that successfully, then do a few decent tests i really think the work i did on two goals should be enough!
            if (slab_sizes[i-1] == 0)
            //due to the restrictions of the definition slab_sizes[0] has to be >= CHUNK_ALIGN_BYTES, with every following increment being bigger than the last. The only one that can be ==0 is the very last one set after the read values, essentially equivalent to a /0 in a string -> if that is reached, break
                break;
            size = slab_sizes[i-1];
        } else if (size >= settings.slab_chunk_size_max / factor) {//remember: size <= settings.slab_chunk_size_max is already true because of restrictions in _parse_slab_sizes
            break;
        }
        /* Make sure items are always n-byte aligned */
        if (size % CHUNK_ALIGN_BYTES)
            size += CHUNK_ALIGN_BYTES - (size % CHUNK_ALIGN_BYTES);

        slabclass[i].size = size;
        //slabclass[i].perslab = settings.slab_page_size / slabclass[i].size; //not needed i dont think
        if (slab_sizes == NULL)//if slab_sizes[] wasnt initialised with _parse_slab_sizes -> use_slab_sizes, 
        //then we just set that each slabclass[i].size is bigger than slabclass[i-1].size by a factor of 'factor'
            size *= factor;//default factor is 1.25? https://github.com/memcached/memcached/blob/490a4aa483e0073735d636c57ed5a7056e06ada3/memcached.c#L5805
            //or from https://github.com/memcached/memcached/blob/490a4aa483e0073735d636c57ed5a7056e06ada3/memcached.c#L5785C1-L5788C32
        
        //if (settings.verbose > 1) {
        //    fprintf(stderr, "slab class %3d: chunk size %9u perslab %7u\n",
        //            i, slabclass[i].size, slabclass[i].perslab);
        //}//also not needed for our analysis, just outputs dialogue for the user
    }

    power_largest = i;
    slabclass[power_largest].size = settings.slab_chunk_size_max;
    //slabclass[power_largest].perslab = settings.slab_page_size / settings.slab_chunk_size_max;
    //if (settings.verbose > 1) {
    //    fprintf(stderr, "slab class %3d: chunk size %9u perslab %7u\n",
    //            i, slabclass[i].size, slabclass[i].perslab);
    //}//also not needed for our analysis, just outputs dialogue for the user

    /* for the test suite:  faking of how much we've already malloc'd */
    /*
    {
        char *t_initial_malloc = getenv("T_MEMD_INITIAL_MALLOC");
        if (t_initial_malloc) {
            int64_t env_malloced;
            if (safe_strtoll((const char *)t_initial_malloc, &env_malloced)) {
                mem_malloced = (size_t)env_malloced;
            }
        }

    }
    */ //Also not relevant to us as it checks for an evironemnt variable and sets a value for a global variable we dont use in our experiment

    
    //if (do_slab_prealloc) {
    //    if (!reuse_mem) {
    //        slabs_preallocate(power_largest);
            /* Preallocate as many slab pages as possible (called from slabs_init)
            on start-up, so users don't get confused out-of-memory errors when
            they do have free (in-slab) space, but no space to make new slabs.
            if maxslabs is 18 (POWER_LARGEST - POWER_SMALLEST + 1), then all
            slab types can be made.  if max memory is less than 18 MB, only the
            smaller ones will be made.  */
            //static void slabs_preallocate (const unsigned int maxslabs);
    //    }
    //} //Also not relevant to us as this preallocates slabs based in a boolean passed into slabs_init() but doesnt change any values we're analysing
}