// #include <stdlib.h>
// #include <stdio.h>
// #include <string.h>

// void quicksort(int lo, int hi, int base[])
// { 
//   int i,j;
//   int pivot,temp;
//   printf("-----------------------------------\n");
//   printf("lo: %d, hi: %d\n", lo, hi);
//   printf("pivot: %d\n", base[hi]);
//   if (lo<hi) {
//     for (i=lo,j=hi,pivot=base[hi];i<j;) {
//       while (i<j && base[i]<pivot) i++;
//       while (j>i && base[j]>pivot) j--;
//       printf("i: %d, j: %d\n", i, j);
//       printf("base[i]: %d, base[j]: %d\n", base[i], base[j]);
//       if (i<j) { temp=base[i]; base[i]=base[j]; base[j]=temp; }
//     }
//     temp=base[i]; base[i]=pivot; base[hi]=temp;
//     quicksort(lo,i-1,base);  quicksort(i+1,hi,base);
//   }
//   printf("###########################################\n");
// }

// int cmpint(const void * i, const void * j)
// {
//   int vi = *((int *) i);
//   int vj = *((int *) j);
//   if (vi == vj) return 0;
//   if (vi < vj) return -1;
//   return 1;
// }

// #define NITER 10

// int main(int argc, char ** argv)
// {
//   // int n, i, j;
//   // int * a, * b;

//   // if (argc >= 2) n = atoi(argv[1]); else n = 100000;
//   // a = malloc(n * sizeof(int));
//   // b = malloc(n * sizeof(int));
//   // for (j = 0; j < NITER; j++) {
//   //   for (i = 0; i < n; i++) b[i] = a[i] = rand() & 0xFFFF;
//   //   quicksort(0, n - 1, a);
//   // }
//   // qsort(b, n, sizeof(int), cmpint);
//   // for(int i = 0; i < n; i++) {
//   //   printf("a:%d, b:%d \n", a[i], b[i]);
//   // }
//   int a[5] = {5, 4, 3, 2, 1};
//   printf("Before sorting: ");
//   for(int i = 0; i < 5; i++) {
//     printf("%d ", a[i]);
//   }
//   printf("\n");
//   quicksort(0, 4, a);
//   printf("After sorting: ");
//   for(int i = 0; i < 5; i++) {
//     printf("%d ", a[i]);
//   }
//   printf("\n");
// //   for (i = 0; i < n; i++) {
// //     if (a[i] != b[i]) { printf("Bug!\n"); return 2; }
// //   }
// //   printf("OK\n");
//   return 0;
// }
#include <stdio.h>
int main(){
  int a[5] = {5, 4, 3, 2, 1};
  a[1]=a[2];
  for(int i=0;i<5;i++){
    // a[i]=i+1;
    printf("%d ", a[i]);
  }
  return 0;
}