#include<errno.h>
//#include<stdlib.h>

bool safe_strtoull(const char *str, uint64_t *out) {
    assert(out != NULL);
    errno = 0;
    *out = 0;
    char *endptr;
    unsigned long long ull = strtoull(str, &endptr, 10);
    if ((errno == ERANGE) || (str == endptr)) {
        return false;
    }

    if (xisspace(*endptr) || (*endptr == '\0' && endptr != str)) {
        if ((long long) ull < 0) {
            if (memchr(str, '-', endptr - str) != NULL) {
                return false;
            }
        }
        *out = ull;
        return true;
    }
    return false;
}

//his solution: pre-process, sodass __errno_location() mit in den dfinitionen ist
//-> make a new file with just #include<errno.h> and the safe_strtoull(...){...} method and pre-process:
//gcc -P -E test_errno.c -o test_errno.i
//to create test.i
//(If you use the -E option, nothing is done except preprocessing) (so just the define replacements etc before compilation?)
//.i is pre-processed C, ohne compiler-direktiven, wird dann zu assembler/bytecode uebersetzt (um eigentlich zu laufen)
//(-P inhibits generation of linemarkers in the output from the preprocessor) (e.g. # ... zeigt wo was herkommt, dies lassen wir aus)
//All this does here is replace 
//#include<errno.h>
//in test_errno.c, with:
//extern int *__errno_location (void) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
//in test_errno.i
//(mit .i koennen wir somit auch leicht sehen woher type und methoden definitionen kommen!)
//somit koennen wir feststellen, errno.h gibt uns nur die __errno_location und sonst gar nichts
//und diese ist "extern" definiert, d.h. sie ist im standard C dabei
//-> wir koennen diese also einfach umschreiben und definieren
//z.B. umdefinieren zu:
//int real_errno = 0; // or int real_errno = __VERIFIER_nondet_int();
//int * __errno_location (void) __attribute__ ((__nothrow__ , __leaf__)) {
//or maybe also this?: 
//int *__errno_location (void) {
//    return &real_errno;
//} //which obviously just always sets __errno_location to return the adresse of the set value 0. 
//But i think i can easily modify this. as long as the real adresse of an int is returned.
//e.g. pseudocode: 
//unsigned long long given nondet_unsigned_long_long_X();
//if (ull>MAX_UUL || ull<0) {real_errno = 34} else{real_errno = 0}
//or something like that
//might also be easier to just remodel errno, knowing what it does, just calling it something else, 
//rather than going through the headache of working with predefined methods

//but either way start simple, start by completely leaving out error cases, remember to stick to the workflow!!!!!!!!!!!!!!!!!!

//(although this one is necessary for the functionality for the rest of the safe_strtoull, as an error escapes with a return false.
//to circumvent this you can also just limit the wertebereich with if(...){abort();} so that return false can never be reached)

//it is also a perfectly valid experiment to remove the guard and check if an error can occur (which i know it will, but its a viable experiment)





//wenn wir jetzt noch #include<stdlib.h> zufuegen und wieder pre-processen, bekommen wir eine menge extra definiert methoden, aber am wichtigsten:
//extern unsigned long long int strtoull (const char *__restrict __nptr,
//     char **__restrict __endptr, int __base)
//     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
//was, wie bei __errno_location eine extern definierte methode ist, welche wir jetzt neu definieren koennen:
//unsigned long long int strtoull (const char *__restrict __nptr, char **__restrict __endptr, int __base){
    //pseudocode: 
    //if(numeric value from __nptr>ULL_MAX){
    //    real_errno = 34;
    //}
    //... restliche methode
//}
//so koennen wir auch errno nachbauen, und dabei auch gleich stroull nachbauen (somit ist aber auch das normale/echte stroull ueberschrieben)

//alternative welche Thomas voschlaegt:
//einen wrapper um stroull rumbauen, und dabei noch extra funktionalitaet einbauen, z.B.:
//unsigned long long strtoull_model(...){
//    strtoull(...);
    //some other stuff
//    if(...){
//        real_errno = 24;
//    }
//}

//will have to rework a little though in this case because im pretty sure ESBMC doesnt understand stroull either

