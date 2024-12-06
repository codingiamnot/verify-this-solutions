method max(s:seq<int>) returns (r:int)
requires |s|>0
ensures 0 <= r < |s|
ensures forall i :: 0<=i < |s| ==> s[i] <= s[r]
{
    var x := 0;
    var y := |s|-1;

    while(x != y)
    invariant 0 <= x <= y < |s|
    invariant forall i:int :: 0 <=i < x ==> s[i] <= s[x] ||s[i] <= s[y]
    invariant forall i:int :: y < i < |s| ==> s[i] <= s[x] || s[i] <= s[y]
    {
        if(s[x] <= s[y])
        {
            x := x+1;
        }
        else
        {
            y := y-1;
        }  
    }

    return x;
}