#include <stdio.h>

int main (int argc, char **argv) {
  int result[10][10];

  transform {
    for (unsigned x : 10, unsigned y : 10) {
      result[x][y] = x + y;
    }
  } by {
    split x into (unsigned x_outer, unsigned x_inner : 4);
    unroll x_inner;
  }
  
  transform {
    for (unsigned x : 10) {
      for (unsigned y : 10) {
        printf("%2d ", result[x][y]);
      }
      printf("\n");
    }
  } by {}

  return 0;
}
