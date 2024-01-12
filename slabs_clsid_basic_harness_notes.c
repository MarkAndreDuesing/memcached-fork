/*
 * Slabs memory allocation, based on powers-of-N. Slabs are up to 1MB in size
 * and are divided into chunks. The chunk sizes start off at the size of the
 * "item" structure plus space for a small key and value. They increase by
 * a multiplier factor from there, up to half the maximum slab size. The last
 * slab size is always 1MB, since that's the maximum item size allowed by the
 * memcached protocol.
 */

////#include "memcached.h"
////#include "storage.h"
//#include <sys/mman.h>
//#include <sys/stat.h>
//#include <sys/socket.h>
//#include <sys/resource.h>
//#include <fcntl.h>
//#include <netinet/in.h>
//#include <errno.h>
//#include <stdlib.h>
//#include <stdio.h>
//#include <string.h>
//#include <signal.h>
//#include <assert.h>
//#include <pthread.h>


//In memcached.h the basic definition of POWER_SMALLEST, POWER_LARGEST and MAX_NUMBER_OF_SLAB_CLASSES are given:
//https://github.com/memcached/memcached/blob/master/memcached.h#L117
/* Slab sizing definitions. */
#define POWER_SMALLEST 1
#define POWER_LARGEST  256 /* actual cap is 255 */
//#define SLAB_GLOBAL_PAGE_POOL 0 /* magic slab class for storing pages for reassignment */
#define CHUNK_ALIGN_BYTES 8
/* slab class max is a 6-bit number, -1. */
#define MAX_NUMBER_OF_SLAB_CLASSES (63 + 1)
//(included the other definitions in the block too as they might be useful for comprehension)
//https://github.com/search?q=repo%3Amemcached/memcached%20POWER_LARGEST&type=code
//https://github.com/search?q=repo%3Amemcached/memcached%20POWER_SMALLEST&type=code
//https://github.com/search?q=repo%3Amemcached/memcached%20MAX_NUMBER_OF_SLAB_CLASSES&type=code
//These are fixed/arent changed anywhere and are used for comparisons. (dont confuse POWER_LARGEST with power_largest)
//in some situations MAX_NUMBER_OF_SLAB_CLASSES is used for max limit on loops too, instead of POWER_LARGEST, despite being set to different values

//other definitions in memcached.h that might also be useful for comprehension:
/*
 * Valid range of the maximum size of an item, in bytes.
 */
//#define ITEM_SIZE_MAX_LOWER_LIMIT 1024
//#define ITEM_SIZE_MAX_UPPER_LIMIT 1024 * 1024 * 1024 
//probably related to settings.item_size_max, investigate further. yes it is, they are used in memcached.c:
/*
if (settings.item_size_max < ITEM_SIZE_MAX_LOWER_LIMIT) {
        fprintf(stderr, "Item max size cannot be less than 1024 bytes.\n");
        exit(EX_USAGE);
    }
if (settings.item_size_max > (ITEM_SIZE_MAX_UPPER_LIMIT)) {
        fprintf(stderr, "Cannot set item size limit higher than a gigabyte.\n");
        exit(EX_USAGE);
    }
//there are also more if cases here that help with comprehension of settings.item_size_max. look into more later
also: https://github.com/memcached/memcached/blob/490a4aa483e0073735d636c57ed5a7056e06ada3/doc/memcached.1#L141
in https://github.com/memcached/memcached/blob/490a4aa483e0073735d636c57ed5a7056e06ada3/memcached.c#L5242 : 
the execution of the -I command occurs, which changes settings.item_size_max. k/K or m/M can be included, 
denoting kilo or mega bytes -> multiplication of result by *1024 or *1024*1024. Then the desired value is read in from a string by atoi()
but not just any value can be read in, cause a bit after that, starting at https://github.com/memcached/memcached/blob/490a4aa483e0073735d636c57ed5a7056e06ada3/memcached.c#L5739
safety checks are used to make sure item_size_max is within the limits of ITEM_SIZE_MAX_LOWER_LIMIT and ITEM_SIZE_MAX_UPPER_LIMIT
the safety checks there also limit item_size_max through other variables like settings.maxbytes and settings.slab_chunk_size_max, but this probably goes beyond the scope of what we need
one thing to potentially keep in mind for slabs_init() implementation is this:     
if (settings.item_size_max % settings.slab_chunk_size_max != 0) {
    fprintf(stderr, "-I (item_size_max: %d) must be evenly divisible by slab_chunk_max (bytes: %d)\n", 
    settings.item_size_max, settings.slab_chunk_size_max); }
*/
//as safety checks in main() from memcached.c
//the name max-item-size instead of item_size_max also comes up a few times, watch out for that. Relevant for us might be, this line from memcached/doc/memcached.1:
/*
.B \-I, --max-item-size=<size>
Override the default size of each slab page. The default size is 1mb. Default
value for this parameter is 1m, minimum is 1k, max is 1G (1024 * 1024 * 1024).
Adjusting this value changes the item size limit.
*/
//oddly enough it seems like the slabs maximum size is 1mb but the item maximum size is 1gb, so how does that work out? investigate further

//restart_set_kv(ctx, "item_size_max", "%d", settings.item_size_max); doesnt seem to change the values, just read them in/save them

typedef struct {
    unsigned int size;      /* sizes of items */
    unsigned int perslab;   /* how many items per slab */

    void *slots;           /* list of item ptrs */
    unsigned int sl_curr;   /* total free items in list */

    unsigned int slabs;     /* how many slabs were allocated for this class */

    void **slab_list;       /* array of slab pointers */
    unsigned int list_size; /* size of prev array */
} slabclass_t;
//I think out of this structure I only need size (and maybe perslab) fields

static slabclass_t slabclass[MAX_NUMBER_OF_SLAB_CLASSES];//MAX_NUMBER_OF_SLAB_CLASSES defined in memcached.h as 63 + 1
/* slab class max is a 6-bit number, -1. */
//#define MAX_NUMBER_OF_SLAB_CLASSES (63 + 1)
//what does this mean though, what are there 64 items of now?

//there are potentially more static variables I need here, check again

static int power_largest;
//power_largest, much like POWER_LARGEST and POWER_SMALLEST also seems to be set and then never changed, but its set in slabs_init
//But i think theyre both only used for boolean comparison checks (typically also with POWER_SMALLEST)


//settings.item_size_max is part of the massive struct in memcached.h https://github.com/memcached/memcached/blob/master/memcached.h#L452
//there its set under https://github.com/memcached/memcached/blob/master/memcached.h#L476:
//int item_size_max;        /* Maximum item size */
//We only need the one field, which is set in https://github.com/memcached/memcached/blob/490a4aa483e0073735d636c57ed5a7056e06ada3/memcached.c#L258 by settings_init() as:
//settings.item_size_max = 1024 * 1024; /* The famous 1MB upper limit. */
//if 1024*1024 refers to 1MB, then 1024 refers to 1kB and 1 refers to 1Byte I would guess
//I think this one could still be changed at various locations though, investigate further:
//https://github.com/search?q=repo%3Amemcached%2Fmemcached%20settings.item_size_max&type=code
//https://github.com/memcached/memcached/blob/490a4aa483e0073735d636c57ed5a7056e06ada3/memcached.c#L5242 //settings.item_size_max = size_max;
//https://github.com/memcached/memcached/blob/490a4aa483e0073735d636c57ed5a7056e06ada3/memcached.c#L5244 //settings.item_size_max = atoi(buf);
//https://github.com/memcached/memcached/blob/490a4aa483e0073735d636c57ed5a7056e06ada3/memcached.c#L1976 //APPEND_STAT("item_size_max", "%d", settings.item_size_max);
//https://github.com/memcached/memcached/blob/490a4aa483e0073735d636c57ed5a7056e06ada3/memcached.c#L4523 //restart_set_kv(ctx, "item_size_max", "%d", settings.item_size_max);
//ask thomas what those last 2 methods migt be referring to

//I think through:
//https://github.com/memcached/memcached/blob/490a4aa483e0073735d636c57ed5a7056e06ada3/storage.c#L1170 : 
//(in storage_init_config()) : s->ext_wbuf_size = 1024 * 1024 * 4;
//and 
//https://github.com/memcached/memcached/blob/490a4aa483e0073735d636c57ed5a7056e06ada3/storage.c#L1401 : 
//"-I (item_size_max: 'settings.item_size_max') cannot be larger than ext_wbuf_size: 'ext_cf->wbuf_size'\n",
//we can also define a limit: settings.item_size_max <= 1024 * 1024 * 4
//I might have that wrong though, mixing up ext_wbuf_size and wbuf_size, only research more if required

//these are also set here in setting_init():
//settings.slab_page_size = 1024 * 1024; /* chunks are split from 1MB pages. */
//settings.slab_chunk_size_max = settings.slab_page_size / 2;
//those are relevant for our slabs_init() implementation and could still be changed elsewhere, investigate later


//still have to look at slabclass[*].size:
//...


/*
 * Figures out which slab class (chunk size) is required to store an item of
 * a given size.
 *
 * Given object size, return id to use when allocating/freeing memory for object
 * 0 means error: can't store such a large object
 */
//so starting at the smallest possible slab chunk size: res = POWER_SMALLEST = 1 and going up from there, 
//to see what the smallest possible slab class is that can fit an object of size 'size' (which we then use for allocating or freeing memory space of that size)
//return 0 meaning either size is 0 or size is too large seems like a problem, see how this output is handled in methods that use slabs_clsid
//but im guessing POWER_SMALLEST and by extension res doesnt directly refer to the size, but the size class. 
//e.g. im guessing we might have slabclass[res].size -> slabclass[1].size = 1; slabclass[2].size = 2; slabclass[3].size = 4; slabclass[1024].size = 2^1023
//or something like that. point is i think res doesnt directly refer to the size, but the class, figure out what those classes are!
unsigned int slabs_clsid(const size_t size) {
    int res = POWER_SMALLEST;

    if (size == 0 || size > settings.item_size_max)
        return 0;
    //so at this point in the method: 1 <= size <= settings.item_size_max (and by extent settings.item_size_max >=1) -> precondition for rest of method., 
    //then we can make postcondition that checks if return 0 is possible in any other way, cause we removed the only way it should be.
    //theres no way res can be <1. can power_largest be <1, that might be worth asserting/investigating
    while (size > slabclass[res].size)
    //while the object were looking at is bigger than the class were investigating (size > slabclass[res].size), 
    //compare to check if the slab class were investigating is the biggest one, then increment to the next class size.
    //if the class size we compared to is the biggest size possible, we return the biggest possible: power_largest
        //(Does that mean settings.item_size_max = power_largest = POWER_LARGEST ? Otherwise if power_largest < settings.item_size_max, 
        //then the size of the object were looking at could be smaller than settings.item_size_max but bigger than power_largest, couldnt it?
        //look into how power_largest is set/defined again)
    //if res isnt equal to power_largest, we see if the increment: size > slabclass[res+1].size
    //remember not to mix up ++i and i++ !
    //if res compares to power_largest an then increments, isnt it possible that slabclass[res+1].size doesnt exist? -> assertion 
    //(but i think this case is caught by return power_largest; preventing another while-loop check)

    //now that i think about it, why do we start at size>slabclass[1].size and not size>slabclass[0].size, look into again!!!
        if (res++ == power_largest)     /* won't fit in the biggest slab */
            return power_largest;
    return res;
    //if res is the biggest class of slab size, return that biggest class id (power_largest), otherwise increment res and check again
}
// i guess surely power_largest != settings.item_size_max, otherwise we wouldnt even bother with the comparison case and return power_largest.
// but then what happens if the size is bigger than the largest slab and it wont fit, what do we do from there, why doesnt it return an error at that point, and instead return the biggest slab class id?
// also if slabclass[power_largest].size > settings.item_size_max then the return power_largest; case is never reachable, right?
// if slabclass[power_largest].size < size <= settings.item_size_max then return power_largest; alsways occurs? -> assertion!

//Generally make a few assertions comparing the 3 variables with symbolic ranges and expected results

//from the description of item_size_ok() in items.c#l380 we can infer that:
//If 'return slabs_clsid(...) != 0' , then:
/**
 * Returns true if an item will fit in the cache (its size does not exceed
 * the maximum for a cache entry.)
 */
//thereby, if size <= settings.item_size_max: an item will fit in the cache (its size does not exceed the maximum for a cache entry.)
//https://github.com/memcached/memcached/blob/master/items.c#L380C13-L380C13


//might also have to understand, recreate and find all places where slabclass[*].size is set, like in:
//https://github.com/memcached/memcached/blob/master/slabs.c#L272
//it seems theyre only ever set in slabs.c:
/*
while (++i < MAX_NUMBER_OF_SLAB_CLASSES-1) {//make sure i understand this ++i correctly again. does this mean, at the end power_largest = i = MAX_NUMBER_OF_SLAB_CLASSES-1 = 63 ? unless a break occurs before the end of the while loop i guess
//...
slabclass[i].size = size;
slabclass[i].perslab = settings.slab_page_size / slabclass[i].size;
//...
}
power_largest = i;
slabclass[power_largest].size = settings.slab_chunk_size_max;
slabclass[power_largest].perslab = settings.slab_page_size / settings.slab_chunk_size_max;
*/
//slabs_init is also only called once with given values, look into what those are exactly
// also look into the values these are set too here: size; settings.slab_page_size; settings.slab_chunk_size_max;
//int slab_chunk_size_max;  /* Upper end for chunks within slab pages. */
//int slab_page_size;     /* Slab's page units. */

//Rather getting too lost in all the size definition i should just get started with the harness and simple modelling. can do the research later too!!!
//for now just write down basic stuff, refine and understand better later


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

    memset(slabclass, 0, sizeof(slabclass));

    while (++i < MAX_NUMBER_OF_SLAB_CLASSES-1) {
        if (slab_sizes != NULL) {
            if (slab_sizes[i-1] == 0)
                break;
            size = slab_sizes[i-1];
        } else if (size >= settings.slab_chunk_size_max / factor) {
            break;
        }
        /* Make sure items are always n-byte aligned */
        if (size % CHUNK_ALIGN_BYTES)
            size += CHUNK_ALIGN_BYTES - (size % CHUNK_ALIGN_BYTES);

        slabclass[i].size = size;
        slabclass[i].perslab = settings.slab_page_size / slabclass[i].size;
        if (slab_sizes == NULL)
            size *= factor;
        if (settings.verbose > 1) {
            fprintf(stderr, "slab class %3d: chunk size %9u perslab %7u\n",
                    i, slabclass[i].size, slabclass[i].perslab);
        }
    }

    power_largest = i;
    slabclass[power_largest].size = settings.slab_chunk_size_max;
    slabclass[power_largest].perslab = settings.slab_page_size / settings.slab_chunk_size_max;
    if (settings.verbose > 1) {
        fprintf(stderr, "slab class %3d: chunk size %9u perslab %7u\n",
                i, slabclass[i].size, slabclass[i].perslab);
    }

    /* for the test suite:  faking of how much we've already malloc'd */
    {
        char *t_initial_malloc = getenv("T_MEMD_INITIAL_MALLOC");
        if (t_initial_malloc) {
            int64_t env_malloced;
            if (safe_strtoll((const char *)t_initial_malloc, &env_malloced)) {
                mem_malloced = (size_t)env_malloced;
            }
        }

    }

    if (do_slab_prealloc) {
        if (!reuse_mem) {
            slabs_preallocate(power_largest);
        }
    }
}


//work to be done: 
//model part of slabs_init that sets power_largest. 
//look into and potentially model segments that set settings.item_size_max
//model an array/struct of slabclass[res].size that realistically recreates the correct slab sizes and their increments (static array, i think?, can you use x[...] for dynamic arrays?)

//can check paths to see if theyre only reachable under our desired conditions

//https://github.com/memcached/memcached/blob/master/slabs.c#L90 //slabs_clsid
//https://github.com/memcached/memcached/blob/master/slabs.c#L337 //grow_slab_list (interesting but most likely wont have time)

//power_largest:
//https://github.com/memcached/memcached/blob/master/slabs.c#L271 //value changed/set in slabs_init
//https://github.com/memcached/memcached/blob/master/slabs.c#L293 //i think this is an error method that uses but doesnt change power_largest, so probably not relevant, but not sure



//Until presentation:
//none of this accounts for stuff like time for sport either
//6 days for goal 2:
//understand method and its uses (what is variable size and where is the method used)!!! -> 0.5 day
//understand and explain methods used in the analysed method (POWER_SMALLEST, settings.item_size_max, slabclass[res].size, power_largest) -> 0.75 day
//implement simple harness and explain it -> 0.75 day
//going to have to model slabs_init as well -> 1 day -> FINISHED BY SATURDAY EVENING AT THE LATEST!!!
//make increasingly complex harness, test for relevant properties, investigate counterexamples and assertions -> 3 days

//4 days for related work, discussion and conclusion and improved tool description first (at least finish for the most part)
//conclusion is good buildup for presentation content?

//3 days for presentation: 
//recap everything important, all the details
//need to do related work, discussion and conclusion and improved tool description first (at least finish for the most part)
//check if i can present in 10 minutes and reherse 
//think of questions they could ask
//include mindmap in presentation somehow?

//also rewatch vods and take notes and scientific writing!!!

//discussion on further work that could be done: initialise and verify more of slabclass by setting the other fields in the struct. this reuires the other methods in slabs.c, which would also have to be analysed for correctness
//slab_list in slabs_prefill_global, slabs_rebalance_finish, grow_slab_list, do_slabs_newslab and slabs_fixup
//perslabs in slabs_init
//slots in slabs_fixup, slabs_rebalance_alloc, do_slabs_free, do_slabs_free_chunked and do_slabs_alloc
//sl_curr in slabs_fixup, slabs_rebalance_alloc, do_slabs_free, do_slabs_free_chunked and do_slabs_alloc
//list_size in grow_slab_list
//slabs in get_page_from_global_pool, slabs_rebalance_finish and do_slabs_newslab

//much like perslabs, size is slabclass[i].size (or the pointer equivalent p->size) is only set in slabs_ini and never changed!!!
//no other .c or .h file where slabsclass is used/changed either