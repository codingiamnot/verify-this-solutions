method lcp(a : array<int>, x:int, y:int) returns (ans:int)
requires 0 <= x < a.Length
requires 0 <= y < a.Length
ensures x <= x+ans <= a.Length
ensures y <= y+ans <= a.Length
ensures a[x..x+ans] == a[y..y+ans]
{
    var l :int := 0;

    while(x+l < a.Length && y+l < a.Length)
    decreases a.Length - (x+l)
    invariant x+l <= a.Length
    invariant y+l <= a.Length
    invariant a[x..x+l] == a[y..y+l]
    {
        if(a[x+l] == a[y+l])
        {
            l := l + 1;
        }
        else
        {
            break;
        }
            
    }

    return l;
}