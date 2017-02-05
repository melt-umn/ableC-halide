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
    reorder x_inner, y_inner, x_outer, y_outer;*/
    tile x, y into (4, 4);
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
