#include <stdio.h> 
#include <assert.h> 
#include <stdlib.h>
#define DLE 16
#define STX 2
#define ETX 3

extern unsigned char __VERIFIER_nondet_uchar();

int main() {
    unsigned char single_value = __VERIFIER_nondet_uchar();
    unsigned char in[6] = {DLE,STX,single_value,DLE,ETX,'\0'};
    unsigned char out[6];
    int i = 0;
    int j = 0;
    while(in[i] != '\0') {
        switch(in[i]) {
            case(DLE):
                if(in[i+1]==STX || in[i+1]==ETX) {
                out[j] = in[i];
                } else {
                out[j] = in[i];
                out[++j] = DLE;
                };
                break;
            default:
                out[j] = in[i];
                break;
        }
        i++;
        j++;
    }
    out[j] = '\0';
    assert(out[4]==ETX || out[5]==ETX);
    return 0;
}

