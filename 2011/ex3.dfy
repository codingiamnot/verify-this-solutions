ghost function freq_dict_of<T>(a: array<T>): (cm: map<T, nat>)
	reads a
	ensures forall k: T :: k in cm ==> cm[k] == |set i: nat | i < a.Length && a[i] == k|
{
	var r := freq_dict_of_s(a[..]);
	assert forall k: T :: k in r ==> (set i: nat | i < a.Length && a[i] == k) == (set i: nat | i < a.Length && (a[..])[i] == k);
	r
}

ghost function freq_dict_of_s<T>(s: seq<T>): (cm: map<T, nat>)
	ensures forall k: T :: k in cm ==> cm[k] == |set i: nat | i < |s| && s[i] == k|
{
	map e: T {:trigger} | e in (set e': T | e' in s) :: |set i: nat | i < |s| && s[i] == e|
}

ghost predicate unique_a<T>(a: array<T>)
	reads a
{
	forall i, j :: 0 <= i < j < a.Length ==> a[i] != a[j]
}

ghost predicate unique_s<T>(s: seq<T>)
{
	forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

lemma if_not_in_a_and_a_eq_b_then_not_in_b<T>(e: T, a: set<T>, b: set<T>)
	requires e !in a
	requires a == b
	ensures e !in b
{}

method duplets_O_of_n<T(==)>(a: array<T>) returns (duplets: seq<T>)
	requires a.Length >= 4
	requires exists e, e' :: e in a[..] && e' in a[..] && e != e' && freq_dict_of(a)[e] >= 2 && freq_dict_of(a)[e'] >= 2
	ensures unique_s(duplets)
	ensures forall e :: e in duplets ==> (exists i: nat :: i < a.Length && e == a[i]) // all elements of `duplets` are from `a` // redundant???
	ensures forall e :: e in duplets ==> freq_dict_of(a)[e] >= 2 // all elements of `duplets` appear at least twice in `a`
	ensures forall e :: e in a[..] && freq_dict_of(a)[e] >= 2 ==> e in duplets // all elements from `a` that appear at least twice in `a` are in `duplets` // remove "from `a`"??? 
	ensures |duplets| >= 2
{
	var m: map<T, nat> := map[];
	duplets := [];
	var i: nat := 0;
	while i < a.Length
		invariant 0 <= i <= a.Length
		invariant m == freq_dict_of_s(a[..i])
		invariant unique_s(duplets)
		invariant (set e: T | e in duplets) == (set k: T | k in freq_dict_of_s(a[..i]) && freq_dict_of_s(a[..i])[k] >= 2)
		invariant forall e :: e in duplets ==> exists j: nat :: j < i && e == a[j]
		invariant forall e :: e in duplets ==> freq_dict_of_s(a[..i])[e] >= 2
		invariant forall e :: e in a[..i] && freq_dict_of_s(a[..i])[e] >= 2 ==> e in duplets
	{
		ghost var fd := freq_dict_of_s(a[..i]);
		ghost var nfd := freq_dict_of_s(a[..i + 1]);
		assert m == fd;
		m := m[a[i] := (if a[i] in m then m[a[i]] + 1 else 1)];
		forall k: T | k in a[..i + 1]
			ensures k != a[i] ==> fd[k] == nfd[k]
			ensures k == a[i] && k in fd ==> nfd[k] == fd[k] + 1
			ensures k == a[i] && k !in fd ==> nfd[k] == 1
		{
			ghost var s0_i := set j: nat | j < i && a[j] == k;
			ghost var si_ip := set j: nat | i <= j < i + 1 && a[j] == k;
			ghost var s0_ip := set j: nat | j < i + 1 && a[j] == k;
			assert s0_ip == s0_i + si_ip;
			assert (set j: nat | j < i && (a[..i])[j] == k) == s0_i;
			assert (set j: nat {:trigger} | j < i + 1 && (a[..i + 1])[j] == k) == s0_ip;
			if k == a[i] {
				assert si_ip == {i};
			}
		}
		assert fd[a[i] := if a[i] in fd then fd[a[i]] + 1 else 1] == nfd;
		assert m == nfd;
		if m[a[i]] == 2 {
			ghost var sd := set e: T | e in duplets;
			ghost var sdp := set e: T | e in duplets + [a[i]];
			ghost var fd_ge_2 := set k: T | k in fd && fd[k] >= 2; 
			ghost var nfd_ge_2 := set k: T | k in nfd && nfd[k] >= 2; 
			assert fd[a[i]] == 1;
			assert a[i] !in fd_ge_2;
			if_not_in_a_and_a_eq_b_then_not_in_b(a[i], fd_ge_2, sd);
			assert a[i] !in (sd);
			assert a[i] !in duplets;
			assert fd[a[i] := fd[a[i]] + 1] == nfd;
			assert nfd_ge_2 == {a[i]} + fd_ge_2;
			assert sd == fd_ge_2;
			assert sdp == {a[i]} + fd_ge_2;
			assert sdp == nfd_ge_2;
			duplets := duplets + [a[i]];
		}
		i := i + 1;
	}
	assert i == a.Length;
	assert a[..] == a[..i];
	assert forall e :: e in duplets ==> freq_dict_of(a)[e] >= 2;
	assert forall e :: e in a[..] && freq_dict_of(a)[e] >= 2 ==> e in duplets;

	ghost var e, e' :| e in a[..] && e' in a[..] && e != e' && freq_dict_of(a)[e] >= 2 && freq_dict_of(a)[e'] >= 2;
	assert e in duplets;
	assert e' in duplets;
	assert e != e';
	assert |duplets| >= 2;
}

method first_two_duplets(a: array<nat>) returns (f: nat, s: nat)
	requires a.Length >= 4
	requires exists e, e' :: e in a[..] && e' in a[..] && e != e' && freq_dict_of(a)[e] >= 2 && freq_dict_of(a)[e'] >= 2
	// requires clauses above are copied from duplets
	ensures f != s
	ensures exists i :: 0 <= i < a.Length && a[i] == f
	ensures exists i :: 0 <= i < a.Length && a[i] == s
	ensures freq_dict_of(a)[f] >= 2
	ensures freq_dict_of(a)[s] >= 2
{ var l := duplets_O_of_n(a); f := l[0]; s := l[1]; assert l[0] in l; assert l[1] in l; return; }
