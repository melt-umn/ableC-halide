#include <stdio.h>

int main (int argc, char **argv) {
  int result[10][10];
  transform {
    for (unsigned x = 0; x < 10; x++) {
      for (unsigned y = 0; x < 10; x++) {
        result[x][y] = x + 1;
      }
    }
  } by {
    split y into (unsigned y_outer, unsigned y_inner : 3);
  }

  return 0;
}
