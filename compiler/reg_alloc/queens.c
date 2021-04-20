#include <iostream>
#include <vector>
using namespace std;

int N = 8;
vector<int> row(N, 0);
vector<int> col(N, 0);
vector<int> diag1(N + N - 1, 0);
vector<int> diag2(N + N - 1, 0);

void printboard() {
  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < N; ++j) {
      cout << (col[i] == j ? "O" : ".");
    }
    cout << endl;
  }
  cout << "===========" << endl;
}

void func(int c)
{
  if (c == N)
  {
      printboard();
  } 
  else 
  {
    for (int r = 0; r < N; ++r) 
    {
      if (row[r] == 0 && diag1[r + c] == 0 && diag2[r + 7 - c] == 0)
      {
        row[r] = 1;
        diag1[r + c] = 1;
        diag2[r + 7 - c] = 1;
        col[c] = r;
        func(c + 1);
        row[r] = 0;
        diag1[r + c] = 0;
        diag2[r + 7 - c] = 0;
      }
    }
  }
}

int main() {
  func(0);
}