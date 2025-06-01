// #define __FLOAT16_TYPE__ double
// #define __FLOAT32_TYPE__ double 
// #define __FLOAT64_TYPE__ double

// #pragma clang float_control(disable)
#define _Float16 double
// #define _Float32 double
// #define _Float64 double

#include <math.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
int f1(int a,int c,int base[]){
    int b[20];
    a=c;
    return a;
}
int* f2(int a,int c){
    int b[20];
    b[((a+c+2)|2)<<3]=2;
    a=c;
    return a;
}
int main(int argc, char ** argv){
    #ifdef __STDC_NO_FLOAT64__
    printf("_Float64 is disabled\n");
    #else
    printf("_Float64 is enabled\n");
    #endif
    return 0;
}