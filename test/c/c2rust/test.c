// #define __FLOAT16_TYPE__ double
// #define __FLOAT32_TYPE__ double 
// #define __FLOAT64_TYPE__ double

// #pragma clang float_control(disable)
// #define _Float16 double
// #define _Float32 double
// #define _Float64 double

// #include <math.h>
#include <stdlib.h>
// #include <stdio.h>
// #include <string.h>
// static inline double eval_A(int i, int j) { return 1.0/((i+j)*(i+j+1)/2+i+1); }

// void eval_A_times_u(int N, const double u[], double Au[])
// {
//   int i,j;
//   for(i=0;i<N;i++)
//     {
//       Au[i]=0;
//       for(j=0;j<N;j++) Au[i]+=eval_A(i,j)*u[j];
//     }
// }
void eval_AtA_times_u(int N, const double u[], double AtAu[])
{
  double *v = (double *)malloc(N * sizeof(double));
 // for (int i = 0; i < N; i++) v[i] = 0; // 初始化所有元素
//   eval_A_times_u(N,u,v);
//   eval_At_times_u(N,v,AtAu);
  free(v);
}
int main(int argc, char ** argv){
    // #ifdef __STDC_NO_FLOAT64__
    // printf("_Float64 is disabled\n");
    // #else
    // printf("_Float64 is enabled\n");
    // #endif
    return 0;
}