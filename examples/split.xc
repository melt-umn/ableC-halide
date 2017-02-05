#include <stdio.h>

int main (int argc, char **argv) {
  int result[10][10];

  transform {
    for (unsigned x : 11 - 1, unsigned y : 10) {
      result[x][y] = x + y;
    }
    
    for (unsigned x : 10) {
      for (unsigned y : 10) {
        printf("%2d ", result[x][y]);
      }
      printf("\n");
    }
  } by {
    split x into (unsigned x_outer, unsigned x_inner : 4);
    split y into (unsigned y1, unsigned y2 : 2, unsigned y3 : 2, unsigned y4 : 2);
  }

  return 0;
}
