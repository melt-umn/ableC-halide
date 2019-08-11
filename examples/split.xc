#include <stdio.h>

int main (int argc, char **argv) {
  int result[10][10];

  transform {
    for (unsigned x = 0; x <= 11 - 2; x++) {
      for (unsigned y = 0; y < 10; y += 1) {
        result[x][y] = x + y;
      }
    }
  } by {
    split x into (unsigned x_outer, unsigned x_inner : 4);
    split y into (unsigned y1, unsigned y2 : 2, unsigned y3 : 2, unsigned y4 : 2);
  }
  
  forall (unsigned x : 10) {
    forall (unsigned y : 10) {
      printf("%2d ", result[x][y]);
    }
    printf("\n");
  }

  return 0;
}
