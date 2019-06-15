#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>

#define NUM_THREADS 8
#define TILE_DIM 70
#define UNROLL_SIZE 5
#define VECTOR_SIZE 8

#define M 70
#define N 1000
#define P 2000

void matmul(unsigned m, unsigned n, unsigned p,
            float a[m][p], float b[p][n], float c[m][n]) {
  transform {
    forall (unsigned i : m, unsigned j : n) {
      c[i][j] = 0;
      forall (unsigned k : p) {
        c[i][j] += a[i][k] * b[k][j];
      }
    }
  } by {
    split i into (unsigned i_outer,
                  unsigned i_inner : (m - 1) / NUM_THREADS + 1);
    parallelize i_outer into (NUM_THREADS) threads;
    tile i_inner, j into (TILE_DIM, TILE_DIM);
    split k into (unsigned k_outer,
                  unsigned k_unroll : UNROLL_SIZE,
                  unsigned k_vector : VECTOR_SIZE);
    unroll k_unroll;
    vectorize k_vector;
  }
}

void matmul_gold(unsigned m, unsigned n, unsigned p,
                 float a[m][p], float b[p][n], float c[m][n]) {
  transform {
    forall (unsigned i : m, unsigned j : n) {
      c[i][j] = 0;
      forall (unsigned k : p) {
        c[i][j] += a[i][k] * b[k][j];
      }
    }
  } by {}
}

int main(int argc, char **argv) {
  srand(1234);

  // Static to avoid allocating massive arrays on the stack
  static float a[M][P];
  static float b[P][N];
  static float c[M][N];
  static float c_ref[M][N];

  fprintf(stderr, "Building input matrices...\n");
  transform {
    forall (unsigned k : P) {
      forall (unsigned i : M)
        a[i][k] = (float)rand() / (float)RAND_MAX;
      forall (unsigned j : M)
        b[k][j] = (float)rand() / (float)RAND_MAX;
    }
  } by {
    parallelize k;
  }

  struct timeval start, end;

  fprintf(stderr, "Performing matrix multiplication... ");
  gettimeofday(&start, NULL);
  matmul(M, N, P, a, b, c);
  gettimeofday(&end, NULL);
  fprintf(stderr, "%f seconds\n",
          (double) (end.tv_usec - start.tv_usec) / 1000000 +
          (double) (end.tv_sec - start.tv_sec));
  
  fprintf(stderr, "Performing reference matrix multiplication... ");
  gettimeofday(&start, NULL);
  matmul_gold(M, N, P, a, b, c_ref);
  gettimeofday(&end, NULL);
  fprintf(stderr, "%f seconds\n",
          (double) (end.tv_usec - start.tv_usec) / 1000000 +
          (double) (end.tv_sec - start.tv_sec));

  fprintf(stderr, "Checking results are equal... ");
  int error = 0;
  transform {
    forall (unsigned i : M, unsigned j : N) {{
      if (c[i][j] != c_ref[i][j]) {
        //printf("Error at element %d, %d: c = %f, c_ref = %f\n", i, j, c[i][j], c_ref[i][j]);
        error = 1;
      }
    }}
  } by {
    parallelize i;
    vectorize j;
  }

  if (error)
    fprintf(stderr, "fail\n");
  else
    fprintf(stderr, "pass\n");
  
  return error;
}
