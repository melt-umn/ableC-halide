#include <stdio.h>

int main (int argc, char **argv) {
  int result[10][10];

  transform {
    for (unsigned x : 11 - 1, unsigned y : 10) {
      result[x][y] = x + y;
    }
  } by {
    /*split x into (unsigned x_outer, unsigned x_inner : 4);
    split y into (unsigned y_outer, unsigned y_inner : 4);
    reorder x_outer, y_outer, x_inner, y_inner;*/
    tile x, y into (4, 4);
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