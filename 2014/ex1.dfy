method coincidenceCount(a:array<int>, b:array<int>, i:int, j:int) returns (r:int)
requires forall i:int :: 0 <= i < a.Length ==> forall j:int :: i < j < a.Length ==> a[i] < a[j]
requires forall i:int :: 0 <= i < b.Length ==> forall j:int :: i < j < b.Length ==> b[i] < b[j]
requires 0 <= i <= a.Length
requires -1 <= j < b.Length
requires (i == a.Length) || (j == -1) || (b[j] < a[i])
decreases a.Length + b.Length - (i+j)
ensures r == |(set x | x in a[i..]) * (set x | x in b[j+1..])|
{
  if(i == a.Length)
  {
    return 0;
  }

  if(j == b.Length-1)
  {
    return 0;
  }

  if(j+1 < b.Length && b[j+1] < a[i])
  {
    var ans:int := coincidenceCount(a, b, i, j+1);

    assert b[j+1] !in (set x | x in a[i..]);
    assert (set x | x in a[i..]) * (set x | x in b[j+1..]) == (set x | x in a[i..]) * (set x | x in b[j+2..]);
    return ans;
  }

  if(a[i] == b[j+1])
  {
    var ans := coincidenceCount(a, b, i+1, j+1);
    assert a[i] !in (set x | x in b[j+2..]);
    assert b[j+1] !in (set x | x in a[i+1..]);
    assert (set x | x in a[i..]) * (set x | x in b[j+1..]) == {a[i]} + (set x | x in a[i+1..]) * (set x | x in b[j+2..]);
    ans := ans+1;
    return ans;
  }

  assert b[j+1] > a[i];
  assert a[i] !in (set x | x in b[j+1..]);
  assert (set x | x in a[i..]) * (set x | x in b[j+1..]) == (set x | x in a[i+1..]) * (set x | x in b[j+1..]);
  var ans := coincidenceCount(a, b, i+1, j);
  return ans;
}

method main(a:array<int>, b:array<int>) returns (r:int)
requires forall i:int :: 0 <= i < a.Length ==> forall j:int :: i < j < a.Length ==> a[i] < a[j]
requires forall i:int :: 0 <= i < b.Length ==> forall j:int :: i < j < b.Length ==> b[i] < b[j]
ensures r == |(set x | x in a[..]) * (set x | x in b[..])|
{
  var ans:int := coincidenceCount(a, b, 0, -1);  
  return ans;
}