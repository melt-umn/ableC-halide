#include <stdio.h>

int main (int argc, char **argv) {
  int result[10][10];

  transform {
    for (unsigned x : 10, unsigned y : 10) {
      result[x][y] = x + y;
    }
  } by {
    parallelize x into (8) threads;
    vectorize y;
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
