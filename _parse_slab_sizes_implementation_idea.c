//#include <stdlib.h>//for size_t and abort()
#include <stdio.h>
//#include <string.h>//for memset
#include <stdint.h>//for uintX_t types
#include <assert.h>

extern unsigned int __VERIFIER_nondet_uint();

struct settings{
    int chunk_size;
    int slab_chunk_size_max;  /* Upper end for chunks within slab pages. */
    int slab_page_size;       /* Slab's page units. */
} settings;

#define CHUNK_ALIGN_BYTES 8
/* slab class max is a 6-bit number, -1. */
#define MAX_NUMBER_OF_SLAB_CLASSES (63 + 1)

void _parse_slab_sizes(uint32_t *slab_sizes) {
    uint32_t size = 0;
    int i = 0;
    uint32_t last_size = 0;

    for (i = 0; i < MAX_NUMBER_OF_SLAB_CLASSES-2; i++){
        //see original implement as to why it can only go up to 61
        //as in the case of i=62 -> i++=63 -> 63>=MAX_NUMBER_OF_SLAB_CLASSES-1 -> return false
        
        //size = (uint32_t) __VERIFIER_nondet_uint();
        
        //size = last_size+100000;//fixed inputs
        //size = last_size+8456;
        //size = last_size+10000;
        size = last_size+48;

        if(size < settings.chunk_size ||
        size > settings.slab_chunk_size_max ||
        last_size >= size ||
        size <= last_size + CHUNK_ALIGN_BYTES){ //!true cases
            //abort();
            printf("error");//for fixed inputs
            break;
        } 
        slab_sizes[i] = size;//dont need to worry about i++, as we already increment at the end of every loop, and moved the upper limit safety check to the front of the loop
        last_size = size;
    }

    slab_sizes[i] = 0;
}

int main(){

uint32_t slab_sizes[MAX_NUMBER_OF_SLAB_CLASSES];
settings.chunk_size = 48;//set to default value; 
settings.slab_page_size = 1024 * 1024; /* chunks are split from 1MB pages. */
settings.slab_chunk_size_max = settings.slab_page_size / 2;

_parse_slab_sizes(slab_sizes);


printf("[");
unsigned int i;
for(i = 0; i < MAX_NUMBER_OF_SLAB_CLASSES-1; i++) {
    printf("'index;%d, value:%d', ",i,slab_sizes[i]);
}
printf("'index;%d, value:%d']\n, ",i,slab_sizes[i]);
printf("%d\n",settings.slab_chunk_size_max);


//assert(slab_sizes[MAX_NUMBER_OF_SLAB_CLASSES-3] != settings.slab_chunk_size_max);
//assert(slab_sizes[MAX_NUMBER_OF_SLAB_CLASSES-3] == settings.slab_chunk_size_max);
//assert(slab_sizes[MAX_NUMBER_OF_SLAB_CLASSES-2] != 0);
//-> found counterexample for all of these -> correct behaviour
//assert(slab_sizes[MAX_NUMBER_OF_SLAB_CLASSES-2] == 0);//should always be true, and it is according to esbmc -> correct behaviour


return 1;
}