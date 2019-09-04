#include <stdio.h>

int main (int argc, char **argv) {
  int result[10][10];

  transform {
    forall (unsigned x : 10, unsigned y : 10) {
      result[x][y] = x + y;
    }
  } by {
    parallelize x into (8) threads;
    unroll y;
  }
  
  forall (unsigned x : 10) {
    forall (unsigned y : 10) {
      printf("%2d ", result[x][y]);
    }
    printf("\n");
  }

  return 0;
}
