
#include <stdio.h>
#include <stdint.h>

/**
 * Structure for storing items within memcached.
 */
typedef struct _stritem {
    /* Protected by LRU locks */
    struct _stritem *next;                                                          //assuming these adresse pointers can be =NULL
    struct _stritem *prev;                                                          //assuming these adresse pointers can be =NULL
    /* Rest are protected by an item lock */
    struct _stritem *h_next;    /* hash chain next */                               //assuming these adresse pointers can be =NULL
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
} item2;

int main()
{   
    char item;
    printf("\n%ld\n",sizeof(item));
    printf("\n%ld\n",sizeof(item2));

    return 0;
}
