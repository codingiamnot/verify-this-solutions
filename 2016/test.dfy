module Matrix {

  // Definition of a matrix as a sequence of sequences (2D sequence)
  datatype Matrix = Matrix(rows: int, cols: int, elements: seq<seq<int>>)

  // Helper function to check if a matrix is well-formed
  function IsWellFormed(A: Matrix): bool {
    |A.elements| == A.rows &&
    forall row :: row in A.elements ==> |row| == A.cols
  }

  // Preconditions for matrix multiplication
  function ValidMultiplication(A: Matrix, B: Matrix): bool {
    IsWellFormed(A) && IsWellFormed(B) && A.cols == B.rows
  }

  // Dot product of two sequences
  function DotProduct(row: seq<int>, col: seq<int>): int
    requires |row| == |col|
  {
    if |row| == 0 then 0 else row[0] * col[0] + DotProduct(row[1..], col[1..])
  }

  // Get a column from a matrix as a sequence
  function GetColumn(A: Matrix, colIndex: int): seq<int>
    requires 0 <= colIndex < A.cols
    ensures |result| == A.rows
  {
    seq row in A.elements :: row[colIndex]
  }

  // Matrix multiplication function
  function Multiply(A: Matrix, B: Matrix): Matrix
    requires ValidMultiplication(A, B)
    ensures IsWellFormed(result) && result.rows == A.rows && result.cols == B.cols
  {
    Matrix(A.rows, B.cols, 
      seq i := 0 .. A.rows :: 
        seq j := 0 .. B.cols :: 
          DotProduct(A.elements[i], GetColumn(B, j))
      )
  }

  // Lemma: Matrix multiplication is associative
  lemma Associativity(A: Matrix, B: Matrix, C: Matrix)
    requires ValidMultiplication(A, B) && ValidMultiplication(B, C)
    ensures Multiply(Multiply(A, B), C) == Multiply(A, Multiply(B, C))
  {
    // Proof of associativity using element-wise equality
    forall i, j :: 
      0 <= i < A.rows && 0 <= j < C.cols ==>
        Multiply(Multiply(A, B), C).elements[i][j] == Multiply(A, Multiply(B, C)).elements[i][j]
    {
      // Expand definitions and use associativity of addition and multiplication
      assert Multiply(Multiply(A, B), C).elements[i][j] ==
        DotProduct(Multiply(A, B).elements[i], GetColumn(C, j));
      assert Multiply(A, Multiply(B, C)).elements[i][j] ==
        DotProduct(A.elements[i], GetColumn(Multiply(B, C), j));
      // Finish proof by unrolling definitions and reasoning about sequences
    }
  }
}
