#include <stdio.h>

int main (int argc, char **argv) {
  int result[10][10];

  transform {
    for (unsigned x : 10, unsigned y : 10) {
      result[x][y] = x + y;
    }
  } by {
    parallelize x into (8) threads;
    unroll y;
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
