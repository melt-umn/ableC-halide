#include <stdio.h>

int main (int argc, char **argv) {
  int reference[10][10], result[10][10];
  
  for (int x = 3; (x) > -6 + (1 - 2); x--) {
    for (int y = 1; 20 >= y; ((y)) += 2) {
      reference[x + 6][y / 2] = x + y + (1 - 1);
    }
  }

  printf("Reference:\n");
  forall (unsigned x : 10) {
    forall (unsigned y : 10) {
      printf("%2d ", reference[x][y]);
    }
    printf("\n");
  }

  transform {
    for (int x = 3; (x) > -6 + (1 - 2); x--) {
      for (int y = 1; 20 >= y; ((y)) += 2) {
        result[x + 6][y / 2] = x + y + (1 - 1);
      }
    }
  } by {
    split x into (unsigned x_outer, unsigned x_inner : 4);
    split y into (unsigned y1, unsigned y2 : 2, unsigned y3 : 2, unsigned y4 : 2);
  }
  
  printf("Actual:\n");
  forall (unsigned x : 10) {
    forall (unsigned y : 10) {
      printf("%2d ", result[x][y]);
    }
    printf("\n");
  }

  forall (unsigned x : 10, unsigned y : 10) {
    if (result[x][y] != reference[x][y]) {
      return 1;
    }
  }

  return 0;
}
