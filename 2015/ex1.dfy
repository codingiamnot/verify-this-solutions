method helper(a:array<int>, b:array<int>, i:int, j:int, canSkip:bool) returns (r:bool, ghost rem:int)
requires 0 <= i <= a.Length
requires 0 <= j <= b.Length
requires a.Length - i <= b.Length - j
decreases a.Length + b.Length - (i+j)
ensures rem == -1 || i <= rem < a.Length
ensures r == (a[i..] == b[j..j+a.Length-i]) || (canSkip && rem !=-1 && (a[i..rem] + a[rem+1..] == b[j..j+a.Length-i-1]))
{
    if(i == a.Length)
    {
        return true, -1;
    }

    if(a[i] == b[j])
    {
        var ans, rem := helper(a, b, i+1, j+1, canSkip);

        if(ans == true)
        {
            assert (a[i+1..] == b[j+1..j+1+a.Length-(i+1)]) || 
                   (canSkip && (a[i+1..rem] + a[rem+1..] == b[j+1..j+1+a.Length-(i+1)-1]));

            if(a[i+1..] == b[j+1..j+1+a.Length-(i+1)])
            {
                assert a[i] == b[j];
                assert (a[i..] == b[j..j+a.Length-i]);
                return true, rem;
            }

            else
            {
                assert canSkip;
                assert (a[i+1..rem] + a[rem+1..] == b[j+1..j+1+a.Length-(i+1)-1]);
                assert a[i..rem] + a[rem+1..] == b[j..j+a.Length-i-1];
                return true, rem;
            }
        }
        else
        {
            return false, a.Length-1;
        }
    }

    if(canSkip && a.Length-i <= b.Length-j-1)
    {
        var ans, rem := helper(a, b, i+1, j, false);

        if(ans == true)
        {
            assert ans == (a[i+1..] == b[j..j+a.Length-(i+1)]);

            assert a[i+1..] == b[j..j+a.Length-(i+1)];
            assert a[i..i] + a[i+1..] == b[j..j+a.Length-i-1];
            assert i <= i < a.Length && a[i..i] + a[i+1..] == b[j..j+a.Length-i-1];
            return true, i;
        }
        else
        {
            return false, a.Length-1;
        }
    }

    return false, a.Length-1;
}