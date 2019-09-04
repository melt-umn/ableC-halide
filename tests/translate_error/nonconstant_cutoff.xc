#include <stdio.h>

int main (int argc, char **argv) {
  int result[10][10];

  int x_unroll = 4;
  transform {
    forall (unsigned x : 10, unsigned y : 10) {
      result[x][y] = x + y;
    }
  } by {
    split x into (unsigned x_outer, unsigned x_inner : x_unroll);
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
