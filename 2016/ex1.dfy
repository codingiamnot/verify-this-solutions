datatype Matrix = Matrice(vals: seq<seq<int>>, n:int)

predicate isSquareMatrix(mat: Matrix)
{
    mat.n >= 1 && |mat.vals| == mat.n && forall i:int :: 0 <= i < mat.n ==> |mat.vals[i]| == mat.n
}

function getMultiplyElemFunc(a:Matrix, b:Matrix, i:int, j:int, n:int) : (ans:int)
requires n >= 0
requires isSquareMatrix(a)
requires isSquareMatrix(b)
requires a.n == b.n
requires 0 <= i < a.n
requires 0 <= j < a.n
requires 0 <= n <= a.n
{
    if n == 0 then
        0
    else
        assert(n > 0);
        getMultiplyElemFunc(a, b, i, j, n-1) + a.vals[i][n-1] * b.vals[n-1][j]
        
}

function getMultiplyElem(a:Matrix, b:Matrix, i:int, j:int) : (ans:int)
requires isSquareMatrix(a)
requires isSquareMatrix(b)
requires a.n == b.n
requires 0 <= i < a.n
requires 0 <= j < a.n
{
    getMultiplyElemFunc(a, b, i, j, a.n)
}

function getMultiplyElem2Func(a:Matrix, b:Matrix, c:Matrix, i:int, j:int, k1:int, k2:int) : (ans : int)
requires isSquareMatrix(a)
requires isSquareMatrix(b)
requires isSquareMatrix(c)
requires a.n == b.n == c.n
requires 0 <= i < a.n
requires 0 <= j < a.n
requires 0 <= k1 < a.n
requires 0 <= k2 < a.n
decreases (a.n-k1) * a.n + (a.n-k2) 
{
    if k2 < a.n-1 then
        a.vals[i][k1] * b.vals[k1][k2] * c.vals[k2][j] + getMultiplyElem2Func(a, b, c, i, j, k1, k2+1)

    else if k1 < a.n-1 then
        a.vals[i][k1] * b.vals[k1][k2] * c.vals[k2][j] + getMultiplyElem2Func(a, b, c, i, j, k1+1, 0)

    else
        a.vals[i][k1] * b.vals[k1][k2] * c.vals[k2][j]
}

function getMultiplyElem2(a:Matrix, b:Matrix, c:Matrix, i:int, j:int) : (ans : int)
requires isSquareMatrix(a)
requires isSquareMatrix(b)
requires isSquareMatrix(c)
requires a.n == b.n == c.n
requires 0 <= i < a.n
requires 0 <= j < a.n
{
    getMultiplyElem2Func(a, b, c, i, j, 0, 0)
}


function multiply(a: Matrix, b: Matrix) : (r: Matrix)
requires isSquareMatrix(a)
requires isSquareMatrix(b)
requires a.n == b.n 
ensures isSquareMatrix(r)
ensures r.n == a.n
{
    var val_ans: seq<seq<int>> := seq(a.n, i requires 0 <=i < a.n => 
                                        seq(a.n, j requires 0 <= j < a.n => 
                                                getMultiplyElem(a, b, i, j)
                                            )
                                     );

    var ans:Matrix := Matrice(val_ans, a.n);
    ans
}

function multiply2(a:Matrix, b:Matrix, c:Matrix) : (r:Matrix)
requires isSquareMatrix(a)
requires isSquareMatrix(b)
requires isSquareMatrix(c)
requires a.n == b.n == c.n
ensures isSquareMatrix(r)
ensures r.n == a.n
{
    var val_ans: seq<seq<int>> := seq(a.n, i requires 0 <=i < a.n => 
                                        seq(a.n, j requires 0 <= j < a.n => 
                                                getMultiplyElem2(a, b, c, i, j)
                                            )
                                     );

    var ans:Matrix := Matrice(val_ans, a.n);
    ans
}


lemma multiply_assoc(a:Matrix, b:Matrix, c:Matrix)
requires isSquareMatrix(a)
requires isSquareMatrix(b)
requires isSquareMatrix(c)
requires a.n == b.n
requires b.n == c.n
ensures multiply(a, multiply(b, c)) == multiply(multiply(a, b), c)
{
    var x := multiply(a, multiply(b, c));
    var y := multiply(multiply(a, b), c);

    assert x.n == y.n;

    if exists i_dif :: 0 <= i_dif < a.n && exists j_dif :: 0 <= j_dif < a.n && x.vals[i_dif][j_dif] != y.vals[i_dif][j_dif]
    {
        var i_dif :| 0 <= i_dif < a.n && exists j_dif :: 0 <= j_dif < a.n && x.vals[i_dif][j_dif] != y.vals[i_dif][j_dif];
        var j_dif :| 0 <= j_dif < a.n && x.vals[i_dif][j_dif] != y.vals[i_dif][j_dif];

        assert x.vals[i_dif][j_dif] == getMultiplyElem(a, multiply(b, c), i_dif, j_dif);
        
        assume x.vals[i_dif][j_dif] == getMultiplyElem2(a, b, c, i_dif, j_dif);
        assume y.vals[i_dif][j_dif] == getMultiplyElem2(a, b, c, i_dif, j_dif); 
    }

    else
    {
        assert forall i_dif :: 0 <= i_dif < a.n ==> forall j_dif :: 0 <= j_dif < a.n ==> x.vals[i_dif][j_dif] == y.vals[i_dif][j_dif];
        assert forall i_dif :: 0 <= i_dif < a.n ==> x.vals[i_dif] == y.vals[i_dif];
        assert |x.vals| == |y.vals|;
        assert |x.vals| == a.n;
        assert isSquareMatrix(x);
        assert isSquareMatrix(y);
        assert x.vals == y.vals;
    }
         
}