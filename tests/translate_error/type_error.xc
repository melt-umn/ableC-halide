#include <stdio.h>

int main (int argc, char **argv) {
  int result[10][10];

  transform {
    forall (float x : 10, char y : 10) {
      result[x][y] = x + y;
    }
  } by {
    split x into (double x_outer, char *x_inner : 4);
    unroll x_inner;
  }
  
  forall (unsigned x : 10) {
    forall (unsigned y : 10) {
      printf("%2d ", result[x][y]);
      if (result[x][y] != x + y)
        return 1;
    }
    printf("\n");
  }

  return 0;
}
