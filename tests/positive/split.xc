#include <stdio.h>

int main (int argc, char **argv) {
  int result[10][10];

  transform {
    forall (unsigned x : 11 - 1, unsigned y : 10) {
      result[x][y] = x + y;
    }
  } by {
    split x into (unsigned x_outer, unsigned x_inner : 4);
    split y into (unsigned y1, unsigned y2 : 2, unsigned y3 : 2, unsigned y4 : 2);
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
