//Credit: this file builds on rosetta.c, from https://sosy-lab.gitlab.io/research/tutorials/CPAchecker/Specification.html
#include <stdlib.h>
#include <assert.h>

// nondet functions, one for each data type,
// cf. __VERIFIER_nondet_X() at https://sv-comp.sosy-lab.org/2022/rules.php
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
extern long __VERIFIER_nondet_long();
//...

int *track_addr; //global variable
int track_int = 10;
int *track_addr2 = &track_int; //global variable


// this is not a special function. In SV-COMP, the reachability property
// specifies that this function shall never be called, i.e., in LTL:
// G ! call(reach_error())
void reach_error(){assert(0);};
//has to be specifically implemented for ESBMC, unlike __VERIFIER_X()

int termination_test(){
  // # Termination

  while (1) {}; // this is an infinite loop 

  //oddly unreach-call finishes processing (and returns VERIFICATION SUCCESSFUL)
  //unlike properties: valid-memsafety, valid-memclean, no-overflow and termination
  return 1;
}
//--timeout t : configure time limit, integer followed by {s,m,h}
//z.B. --timeout 10s 
//-> ERROR: Timed out

int over_under_flow_test(){
  // # (Signed Integer) Overflows 
  //increment past INT_MAX by 1:
  int int1 = 2147483647; int1++; //-> FALSE_OVERFLOW violation
  //-> Report: "arithmetic overflow on add !overflow("+", int1, 1)"

  // # (Signed Integer) Underflows
  int int2 = -2147483648; int2--; //-> FALSE_OVERFLOW violation. So the name is a bit of a misnomer, and checks underflows too
  //-> Report: "arithmetic overflow on sub !overflow("-", int2, 1)"

  //Its worth noting if I set int x = -2147483650; it doesnt detect the error, 
  //as the value is out of range in the first place, independant of whether we decrement it.
  //-> only a system warning gets called, no ESBMC error.
  //This also probably contributes to no problem being detected with unsigned int x = 4294967295; x++; as it sees x as out of range in the first place?


  // # (Unsigned Integer) Overflows
  unsigned int uint1 = 4294967295; uint1++; //-> should be a violation, but with no-overflow Wrapper it isnt registered as such
       //with the addition of --unsigned-overflow-check to the wrapper, this is detected too

  // # (Unsigned Integer) Underflows 
  unsigned int uint2 = 0; uint2--;


  // # (Unsigned Long Long Integer) Overflows 
  unsigned long long int ull1 = 18446744073709551615; ull1++;
  //despite whats implied by SVComp tests, ESBMC also supports under/overflows from other datatypes, like ull
  //(but once again need --unsigned-overflow-check for the unsigned part, otherwise no error recognised)
  
  // # (Unsigned Long Long Integer) Underflows 
  unsigned long long int ull2 = 0; ull2--;


  // # (Char) Overflows 
  char char1 = 127; char1++;
  //It is also worth noting that char defaults to signed char, not the flexible typing that some literature suggests char (where it could be either signed or unsigned)
  //setting this value as 255, mistaking this for an unsigned char, doesnt lead to an ESBMC error report, as 255 already out of signed char bounds
  
  //To exemplify this again:
  // # (Signed Char) Overflows 
  signed char char2 = 127; char2++;
    // # (Unsigned Char) Overflows 
  unsigned char uchar1 = 255; uchar1++;


  //alternatively to --unsigned-overflow-check, you could attempt to code unsigned int as signed long int -> same max value for overflows
  return 1;
}

int reachability_test(){
  //various reachability assertion methods:

  //__VERIFIER_error();//depricated, but possible
  reach_error();
  //FALSE_REACH -> "file rosetta.c line 18 column 20 function reach_error assertion 0"
  //This tells us that the error was found in reach_error(), rather than the location in the code where reach_error() was reached
  //Alternatively we could just call assert(0); directly to give us the right line in the report:
  assert(0);
  //FALSE_REACH -> "file rosetta.c line 95 column 3 function reachability_test assertion 0"

  if(1 == 0){
    reach_error();//never reached -> no error
  }
  if(1 == 1){
    reach_error();//reachable (always reached) -> FALSE_REACH
  }

  int c = 0;
  if(1 == 0){
    c++;
    return 1; //-> this unreachable code isn't detected
  }//ESBMC unreach-call doesnt actuall detect dead code and unreachable branches. 
  //It just checks if reach_error(); and by extent a false assertion is reached
  
  unsigned int y = __VERIFIER_nondet_int();
  assert(y*y<y);
  // not an overflow with undefined behavior since y is unsigned; (if we include the flag --unsigned-overflow-check to ESBMC it would be an overflow error)
  // Otherwise this is a FALSE_REACH violation as y*y can never be < y for int -> assert(false)

  return 1;
}



//1) valid-free: 

int valid_free_test1(){// -> FALSE_FREE as an already freed memory is freed again
  //FALSE_FREE -> "dereference failure: invalidated dynamic object freed"
  int *out = (int *)malloc(sizeof(int));
  free(out);
  free(out);

  return 1;
}

int valid_free_test2(){// -> FALSE_FREE as static memory doesnt need to be freed
  unsigned char out[6];
  out[5] = '\0';
  free(out); //-> dereference failure: free() of non-dynamic memory -> FALSE_FREE
  //or same result with:
  //unsigned char *ptr = &out; 
  //free(ptr); //attempting to use free on a pointer to a static/non-dynamically allocated array leads to undefined behavior

  return 1;
}

int valid_free_test3(){
  //int *x; // -> dereference failure: invalid pointer freed
  int *x = 0; 
  //int *x = NULL; 
  //int *x = 10000;
  free(&x); //-> dereference failure: free() of non-dynamic memory -> FALSE_FREE
  //-> incorrect, as were attempting to free memory that hasn't been dynamically allocated
  //or same result with:
  //int *ptr = &x; 
  //free(ptr);

  //The pointer x is initialized to 0 (or NULL) -> it isn't pointing to a valid memory location. 
  //Passing an invalid pointer to free results in undefined behavior.
  //int *x = 10000; free(x); is also undefined behavior. Even if the value assigned to the pointer x coincides with an address that may have been previously 
  //allocated, explicitly setting an integer value to a pointer and then trying to free it is still incorrect and leads to undefined behavior.

  return 1;
}

int valid_free_test4(){//-> FALSE_FREE, as free() apparently can't be used with adresse offsets, leading to an incorrect use of free()
//see: https://stackoverflow.com/questions/4744774/can-i-free-by-referencing-an-offset-pointer
  unsigned char *out = (unsigned char *)malloc(sizeof(unsigned char) * 6);
  unsigned char *ptr = out + 10; // Out-of-bounds access
  free(ptr); //-> "Operand of free must have zero pointer offset" -> FALSE_FREE

  return 1;
}



//2) valid-deref:

int valid_deref_test1(){ //-> FALSE_DEREF 
  //as a value outside of the statically allocated array is changed(/dereferenced by out[10]?)
  unsigned char out[6];
  out[10] = '\0';// //out[5] = '\0'; would be correct
  //FALSE_DEREF -> "array bounds violated: array `out' upper bound"
  //or alternatively: 
  unsigned char value = *(out + 10);
  //FALSE_DEREF -> "dereference failure: array bounds violate"

  return 1;
}//Accessing memory beyond the allocated bounds or using incorrect pointer arithmetic can lead to undefined behavior

int valid_deref_test2(){//-> FALSE_DEREF
  //alternatively doing the same as before, but with dynamic memory (malloc) (as opposed to using arrays) 
  unsigned char *out = (unsigned char *)malloc(sizeof(unsigned char) * 6);
  *(out + 10) = '\0'; // Writing beyond the array bounds  // *(out + 5) = '\0'; would be correct
  //or alternatively: 
  unsigned char value = *(out + 10); // Accessing beyond the array bounds
  
  //FALSE_DEREF -> "dereference failure: array bounds violated"
  free(out);

  return 1;
}

int valid_deref_test3(){//dereference freed dynamic memory:
int *ptr = (int *)malloc(sizeof(int));
free(ptr);

*ptr = 42; // Writing to freed memory
//or alternatively:
int value = *ptr; // Accessing freed memory
//-> "dereference failure: invalidated dynamic object" -> FALSE_DEREF

return 1;
}

int valid_deref_test4(){//NULL dereference:
  int y = 10;

  //Valid:
  int *x = &y; //x is a pointer for the adresse of y
  y == *x; //-> valid dereference, takes the value in memory, to which x points

  //Invalid:
  int *z = 0;
  y == *z; //-> invalid as x doesnt point to a valid memory location (0/NULL)
  //-> "dereference failure: NULL pointer" -> FALSE_DEREF

  return 1;
}




//Example for valid-memtrack: true, but valid-memcleanup: false :
int memtrack_t_memcleanup_f_test() {
  //FALSE_MEMCLEANUP -> "dereference failure: forgotten memory: dynamic_1_array"
  track_addr = malloc(sizeof(int)); 
  //free(track_addr);//-> if included, passes both memcleanup and memsafety
  
  //track_addr2 = malloc(sizeof(int)); 
  //free(track_addr2);//-> if included, passes both memcleanup and memsafety
  return 1;
}
//This passes valid-memtrack (and valid memsafety in general), 
//as the allocated space is still reachable over the global variable 'track_addr' until the program ends
//-> the memory is still controllable and isnt lost
//But valid-memcleanup is false, as the space was never freed before program end
//-> correctly registers as FALSE_MEMCLEANUP error but as TRUE for vaild-memsafety


//Example for valid-memtrack: false, and valid-memcleanup: false :
int memtrack_f_memcleanup_f_test(){//-> FALSE_MEMTRACK and FALSE_MEMCLEANUP
  //FALSE_MEMCLEANUP/FALSE_MEMTRACK -> "dereference failure: forgotten memory: dynamic_1_array"
  
  int *p = (int *)malloc(sizeof(int));
  p = 0;//-> lost track of the allocated memory
  //even if we now do free(p); the original memory is still lost

  //It is worth noting however that both porperty checks only report back an error at the end of the main method, 
  //a.k.a. the end of the whole program, rather than at the end of the block for memtrack or when p = 0; is set.
  return 1;
}
//or maybe it just says the error occured there, but it detected it at the appropriate spot for memtrack(?)
//(-> can mention this as a limitation of ESBMC if i can verify this!!!)

int memtrack_cleanup_sumtest(int a, int b){//-> FALSE_MEMTRACK and FALSE_MEMCLEANUP
//memory space is allocated with *x here, but never freed and then the local variable is lost at the end of the method
int *x = malloc(sizeof(int));
*x = a + b;
int y = *x;//-> lose track of pointer x at the end of this block as its only locally defined
//once again though, the ESBMC error report only informs me about an error the end of the entire program
//at the end of main(). Could become an issue if the program doesnt terminate and the end is never reached.
return y;
}
//Different from setting int x = a + b; as that would be a statically initialised local variable that automatically 
//gets freed when the method ends -> static vs dynamic memory allocation



int main() {
  //over_under_flow_test();
  //reachability_test();
  //valid_free_test1();
  //valid_free_test2();
  //valid_free_test3();
  //valid_free_test4();
  //valid_deref_test1();
  //valid_deref_test2();
  //valid_deref_test3();
  //valid_deref_test4();
  //memtrack_t_memcleanup_f_test();
  //memtrack_f_memcleanup_f_test();
  //memtrack_cleanup_sumtest(1,2);
  //termination_test();





//Another FALSE_FREE:

//int *arr = (int *)malloc(5 * sizeof(int));
//free(arr);
//int *ptr3 = arr;
//free(ptr3); // Invalid deallocation


//Another FALSE_FREE: 
//where we show that arrays are non-dynamic memory, even with non-determinism,
//therefore dont need to be freed!
  int n = __VERIFIER_nondet_int();
  if(n >= 7 || n <= 3) {abort();}
  
  //char vals[n];
  //for (unsigned int i = 0; i < n-1; ++i){vals[i] = __VERIFIER_nondet_char();}
  //vals[n-1] = '\0';
  //free(vals);
  
  //it would be correct if you used:
  char *vals = (char *)malloc(sizeof(char) * n);
  for (unsigned int i = 0; i < n-1; ++i){*(vals + i) = __VERIFIER_nondet_char();}
  *(vals + (n-1)) = '\0';  
  free(vals);


  return 0;
}















int malloc_array() {
//After allocating memory using malloc for an array of unsigned char, you can set values at specific indices just like you would with a regular array:
    unsigned char *out = (unsigned char *)malloc(sizeof(unsigned char) * 6);
    //also try this:
    //unsigned char out[6]; 
    unsigned char *pt;
	  pt=out;

    // Set values at specific indices
    out[0] = 'H';//or do: *out = 'H';
    out[1] = 'e';//or do: *(out + 1) = 'e';
    out[2] = 'l';//or do: *(out + 2) = 'l';
    out[3] = 'l';//or do: *(out + 3) = 'l';
    out[4] = 'o';//or do: *(out + 4) = 'o';
    out[5] = '\0';//or do: *(out + 5) = '\0'; // Null-terminate the string

    free(out);// Free the allocated memory when done
    free(pt);// try this-> FALSE_FREE as memory was already freed by free(out)
    return 0;
}


//Test variable length arrays and their allocation in regards to valid-memsafety (are they stack or heap?):
char* read_and_process(int n){
    char vals[n];

    for (unsigned int i = 0; i < n-1; ++i){vals[i] = __VERIFIER_nondet_char();}
  	vals[n-1] = '\0';

    return vals;
}//i think this doesnt set at compiler time
//You can't return arrays from functions in C!
