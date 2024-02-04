void slabs_init(const double factor, const uint32_t *slab_sizes_input) {
    int i = POWER_SMALLEST - 1;
    //...
    unsigned int size = sizeof(item) + settings.chunk_size;
    //...
    while (++i < MAX_NUMBER_OF_SLAB_CLASSES-1) {
        //...
        if (size >= settings.slab_chunk_size_max / factor) {
            break;
        }
        //...
        slabclass[i].size = size;
        if (slab_sizes_input == NULL){
            size *= factor;
        }
    }
    power_largest = i;
    slabclass[power_largest].size = settings.slab_chunk_size_max;
}