#include <stdio.h>

int main (int argc, char **argv) {
  int result[10][10];

  transform {
    for (unsigned x : 10, unsigned y : 10) {
      result[x][y] = x + y;
    }
  } by {
    split x into (unsigned x_outer, unsigned x_inner : 4);
    unroll x;
  }
  
  for (unsigned x = 0; x < 10; x++) {
    for (unsigned y = 0; y < 10; y++) {
      printf("%2d ", result[x][y]);
      if (result[x][y] != x + y)
        return 1;
    }
    printf("\n");
  }

  return 0;
}
