#include <stdio.h>

int main (int argc, char **argv) {
  int result[10][10];

  transform {
    for (unsigned x : 10, unsigned y : 10)
      result[x][y] = x + y;
  } by {
    split x into (unsigned x_outer, unsigned x_inner : 4);
    split y into (unsigned y1, unsigned y2 : 2, unsigned y3 : 2, unsigned y4 : 2);
  }

  unsigned i, j;
  for (i = 0; i < 10; i++) {
    for (j = 0; j < 10; j++) {
      printf("%2d ", result[i][j]);
    }
    printf("\n");
  }

  return 0;
}
