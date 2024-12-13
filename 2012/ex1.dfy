class LRS {
  static function string_to_nat(s: string): (n: nat)
		requires |s| > 0
		requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
		decreases |s|
	{
		if |s| == 1 then
			(s[0] - '0') as nat
		else string_to_nat(s[..|s| - 1]) * 10 + string_to_nat(s[|s| - 1..|s|])
	}
	static predicate nat_gt_0(s: string)
		requires |s| > 0
	{'1' <= s[0] <= '9' && forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9'}
	static function string_to_int(s: string): (n: int)
		requires |s| > 0
		requires s == "0" || (s[0] == '-' && |s| > 1 && nat_gt_0(s[1..])) || nat_gt_0(s)
	{
		if s == "0" then
			0
		else
			if s[0] == '-' then
				(-1) * string_to_nat(s[1..])
			else
				string_to_nat(s)
	}
  static method {:main} Main(args: seq<string>) {
		if (forall arg :: arg in args ==> (|arg| > 0 && (arg == "0" || (arg[0] == '-' && |arg| > 1 && nat_gt_0(arg[1..])) || nat_gt_0(arg)))) && |args| > 1 {
			var a: array<int> := array_from_range(|args|, (i: nat) => assume i < |args|; string_to_int(args[i]));
			var solStart, solLength := DoLRS(a);
			print solStart, "->", solLength, "\n";
		}
  }

  static method DoLRS(a: array<int>) returns (solStart: nat, solLength: nat)
    requires a.Length > 1
		// m-am pierdut
  {
    solStart := 0;
    solLength := 0;
    var sa: SuffixArray := new SuffixArray(a);
    for i := 1 to a.Length - 1
			invariant sa.indexes_in_a(sa.suffixes[..])
		{
      var length := sa.lcp(i);
      if length > solLength {
        solStart := sa.select(i);
        solLength := length;
      }
    }
  }
}

ghost predicate is_mapping_of<T>(a: array<T>, f: nat -> T)
	reads a
{
	forall i: nat {:trigger} :: i < a.Length ==> a[i] == f(i)
}

method array_from_range<T(0)>(n: nat, mapping: nat -> T) returns (mapped: array<T>)
	ensures mapped.Length == n
	ensures is_mapping_of(mapped, mapping)
	ensures fresh(mapped)
{
	mapped := new[n];
	var i: nat := 0;
	while i < n
		invariant 0 <= i <= n
		invariant forall gi :: 0 <= gi < i ==> mapped[gi] == mapping(gi)
	{
		mapped[i] := mapping(i);
		i := i + 1;
	}
}

ghost predicate is_permutation_seq(permutation: seq<nat>)
{
	(forall i: nat, j: nat {:trigger} :: i < j < |permutation| ==> permutation[i] != permutation[j])
		&&
	(forall e: nat {:trigger} :: e in permutation ==> e < |permutation|)
}
ghost predicate is_permutation_array(permutation: array<nat>)
	reads permutation
{is_permutation_seq(permutation[..])}

method range_array(n: nat) returns (mapped: array<nat>)
	ensures mapped.Length == n
	ensures is_mapping_of(mapped, x => x)
	ensures is_permutation_array(mapped)
	ensures fresh(mapped)
{
	mapped := array_from_range(n, x => x);
}

ghost predicate is_reordering_of<T>(a: seq<T>, b: seq<T>)
	requires |a| == |b|
{exists p: seq<nat> {:trigger} :: |p| == |a| && is_permutation_seq(p) && (forall i: nat {:trigger} :: i < |p| ==> a[p[i]] == b[i])}

lemma commutativity_of_reordering<T>(a: seq<T>, b: seq<T>)
	requires |a| == |b|
	requires is_reordering_of(a, b)
	ensures is_reordering_of(b, a)
{
	var p: seq<nat> :| |p| == |a| && is_permutation_seq(p) && (forall i: nat {:trigger} :: i < |p| ==> a[p[i]] == b[i]);
	var p_to_pp: seq<nat> :| |p_to_pp| == |a| && is_permutation_seq(p_to_pp) && (forall i: nat {:trigger} :: i < |p_to_pp| ==> p_to_pp[p[i]] == i && p[p_to_pp[i]] == i) by {
		assume false;
	}
}

lemma transitivity_of_reordering<T>(a: seq<T>, b: seq<T>, c: seq<T>)
	requires |a| == |b| == |c|
	requires is_reordering_of(a, b)
	requires is_reordering_of(b, c)
	ensures is_reordering_of(a, c)
{
	var pab: seq<nat> :| |pab| == |a| && is_permutation_seq(pab) && (forall i: nat {:trigger} :: i < |pab| ==> a[pab[i]] == b[i]);
	var pbc: seq<nat> :| |pbc| == |b| && is_permutation_seq(pbc) && (forall i: nat {:trigger} :: i < |pbc| ==> b[pbc[i]] == c[i]);
	assert exists pac: seq<nat> :: |pac| == |a| && is_permutation_seq(pac) && (forall i: nat {:trigger} :: i < |pac| ==> pac[i] == pab[pbc[i]]) by {
		assume false;
	}
}

class SuffixArray {
	const a: array<int>
	const suffixes: array<nat>
	constructor (a: array<int>) // public
		ensures indexes_in_a(suffixes[..])
		ensures is_sorted(suffixes[..])
		ensures |suffixes[..]| == a.Length
		ensures is_reordering_of(suffixes[..], seq(a.Length, i => i))
	{
		this.a := a;
		var s := range_array(a.Length);
		ghost var old_s: seq<nat> := s[..];
		suffixes := s;
		new;
		sort(suffixes);
		// assert |suffixes[..]| == a.Length;
	}
	method select(i: nat) returns (selected: nat) // public
		requires i < suffixes.Length
		ensures selected == suffixes[i]
	{
		return suffixes[i];
	}
	static function lcp_helper_function<T(==)>(a: seq<T>, b: seq<T>): (l: nat)
		ensures l <= |a| && l <= |b|
		ensures is_common_prefix_func(a, b, l)
		ensures no_larger_common_prefix_exists_func(a, b, l)
	{
		if |a| == 0 || |b| == 0 then
			assert no_larger_common_prefix_exists_func(a, b, 0) by {
				if !no_larger_common_prefix_exists_func(a, b, 0) {
					var ll :| 0 < ll && is_common_prefix_func(a, b, ll);
					// assert forall i: nat {:trigger} :: i < ll ==> elements_at_i_are_in_range(a, b, i);
					assert exists i: nat {:trigger} :: i < ll && !elements_at_i_are_in_range(a, b, i) by {
						assert !elements_at_i_are_in_range(a, b, 0);
					}
				}
			}
			0
		else if a[0] != b[0] then
			assert no_larger_common_prefix_exists_func(a, b, 0) by {
				if !no_larger_common_prefix_exists_func(a, b, 0) {
					var ll :| 0 < ll && is_common_prefix_func(a, b, ll);
					// assert forall i: nat {:trigger} :: i < ll ==> elements_at_i_are_in_range(a, b, i);
					// assert exists i: nat {:trigger} :: i < ll && !elements_at_i_are_in_range(a, b, i) by {
					// 	assert !elements_at_i_are_in_range(a, b, 0);
					// } // TODO: think about why this assert works !!!!!!!!!
					// assert forall i: nat {:trigger} :: i < ll ==> elements_at_i_are_equal(a, b, i);
					assert exists i: nat {:trigger} :: i < ll && !elements_at_i_are_equal(a, b, i) by {
						assert !elements_at_i_are_equal(a, b, 0);
					}
				}
			}
			0
		else
			var r: nat := lcp_helper_function(a[1..], b[1..]);
			assert is_common_prefix_func(a, b, r + 1) by {
				assert is_common_prefix_func(a[1..], b[1..], r);
				assert is_common_prefix_func(a, b, r + 1) by {
					forall i: nat {:trigger} | i < r + 1
						ensures elements_at_i_are_in_range(a, b, i) && elements_at_i_are_equal(a, b, i)
					{
						if i == 0 {
							assert elements_at_i_are_in_range(a, b, 0) && elements_at_i_are_equal(a, b, 0);
						} else {
							assert elements_at_i_are_in_range(a[1..], b[1..], i - 1) && elements_at_i_are_equal(a[1..], b[1..], i - 1);
							assert i - 1 < |a[1..]| && i - 1 < |b[1..]| && a[1..][i - 1] == b[1..][i - 1];
							assert i - 1 < |a| - 1 && i - 1 < |b| - 1 && a[i - 1 + 1] == b[i - 1 + 1];
							assert i < |a| && i < |b| && a[i] == b[i];
							assert elements_at_i_are_in_range(a, b, i) && elements_at_i_are_equal(a, b, i);
						}
					}
				}
			}
			assert no_larger_common_prefix_exists_func(a, b, r + 1) by {
				assert no_larger_common_prefix_exists_func(a[1..], b[1..], r);
				assert forall ll: nat {:trigger} :: r < ll ==> !is_common_prefix_func(a[1..], b[1..], ll);
				assert forall ll: nat {:trigger} :: r + 1 < ll ==> !is_common_prefix_func(a, b, ll) by {
					forall ll: nat {:trigger} | r + 1 < ll
						ensures !is_common_prefix_func(a, b, ll)
					{
						////////////////////////////////////////////////////// commented asserts within this scope unnecessarily increase resource usage
						assert !is_common_prefix_func(a[1..], b[1..], ll - 1);
						// assert !forall i: nat {:trigger} :: i < ll - 1 ==> elements_at_i_are_in_range(a[1..], b[1..], i) && elements_at_i_are_equal(a[1..], b[1..], i);
						assert exists i: nat {:trigger} :: i < ll - 1 && !(elements_at_i_are_in_range(a[1..], b[1..], i) && elements_at_i_are_equal(a[1..], b[1..], i));
						if exists i: nat {:trigger} :: i < ll - 1 && !(elements_at_i_are_in_range(a[1..], b[1..], i) && elements_at_i_are_equal(a[1..], b[1..], i)) {
							var i: nat :| i < ll - 1 && !(elements_at_i_are_in_range(a[1..], b[1..], i) && elements_at_i_are_equal(a[1..], b[1..], i));
							assert !(elements_at_i_are_in_range(a[1..], b[1..], i) && elements_at_i_are_equal(a[1..], b[1..], i));
							assert !(i < |a[1..]| && i < |b[1..]| && a[1..][i] == b[1..][i]);
							assert !(i < |a| - 1 && i < |b| - 1 && a[i + 1] == b[i + 1]);
							assert !(elements_at_i_are_in_range(a, b, i + 1) && elements_at_i_are_equal(a, b, i + 1));
						}
						// assert exists i: nat {:trigger} :: i < ll && !(elements_at_i_are_in_range(a, b, i + 1) && elements_at_i_are_equal(a, b, i + 1));
						// assert !forall i: nat {:trigger} :: i < ll ==> elements_at_i_are_in_range(a, b, i + 1) && elements_at_i_are_equal(a, b, i + 1);
						// assert !is_common_prefix_func(a, b, ll);
					}
				}
			}
			r + 1
	}
	// helper ghost predicates for lcp_helper and lcp_helper_function
		static ghost predicate elements_at_xpi_and_ypi_are_in_range<T>(a: array<T>, x: nat, y: nat, i: nat)
			reads a
		{x + i < a.Length && y + i < a.Length}
		static ghost predicate elements_at_xpi_and_ypi_are_equal<T>(a: array<T>, x: nat, y: nat, i: nat)
			reads a
			requires elements_at_xpi_and_ypi_are_in_range(a, x, y, i)
		{a[x + i] == a[y + i]}
		static ghost predicate elements_at_i_are_in_range<T>(a: seq<T>, b: seq<T>, i: nat)
		{i < |a| && i < |b|}
		static ghost predicate elements_at_i_are_equal<T>(a: seq<T>, b: seq<T>, i: nat)
			requires elements_at_i_are_in_range(a, b, i)
		{a[i] == b[i]}
		static ghost predicate is_common_prefix<T>(a: array<T>, x: nat, y: nat, l: nat)
			reads a
		{forall i: nat {:trigger} :: i < l ==> elements_at_xpi_and_ypi_are_in_range(a, x, y, i) && elements_at_xpi_and_ypi_are_equal(a, x, y, i)}
		static ghost predicate is_common_prefix_func<T>(a: seq<T>, b: seq<T>, l: nat)
		{forall i: nat {:trigger} :: i < l ==> elements_at_i_are_in_range(a, b, i) && elements_at_i_are_equal(a, b, i)}

		static ghost predicate no_larger_common_prefix_exists<T>(a: array<T>, x: nat, y: nat, l: nat)
			reads a
		{!exists ll: nat {:trigger} :: l < ll && is_common_prefix(a, x, y, ll)}
		static ghost predicate no_larger_common_prefix_exists_func<T>(a: seq<T>, b: seq<T>, l: nat)
		{!exists ll: nat {:trigger} :: l < ll && is_common_prefix_func(a, b, ll)}
	//

	method lcp_helper(x: nat, y: nat) returns (l: nat) // private
		requires x <= a.Length && y <= a.Length
		ensures x + l <= a.Length && y + l <= a.Length
		ensures is_common_prefix(a, x, y, l)
		ensures no_larger_common_prefix_exists(a, x, y, l)
		ensures l == lcp_helper_function(a[x..], a[y..])
	{
		l := 0;
		while x + l < a.Length && y + l < a.Length && a[x + l] == a[y + l]
			invariant x + l <= a.Length && y + l <= a.Length
			invariant forall i: nat :: i < l ==> a[x..][i] == a[y..][i]
			// invariant forall i: nat {:trigger} :: x <= i < x + l ==> a[i] == a[i - x + y]
			// invariant forall i: nat {:trigger} :: i < l ==> a[x + i] == a[y + i] // this by itself doesn't work
		{
			l := l + 1;
		}
		assert no_larger_common_prefix_exists(a, x, y, l) by {
			assert x + l >= a.Length || y + l >= a.Length || a[x + l] != a[y + l];
			if x + l >= a.Length || y + l >= a.Length {
				if !no_larger_common_prefix_exists(a, x, y, l) {
					// var ll: nat :| l < ll && is_common_prefix(a, x, y, ll);
					// assert forall i: nat {:trigger} :: i < ll ==> elements_at_xpi_and_ypi_are_in_range(a, x, y, i);
					assert !elements_at_xpi_and_ypi_are_in_range(a, x, y, l);
				}
			} else {
				if !no_larger_common_prefix_exists(a, x, y, l) {
					// var ll: nat :| l < ll && is_common_prefix(a, x, y, ll);
					// assert forall i: nat {:trigger} :: i < ll ==> elements_at_xpi_and_ypi_are_in_range(a, x, y, i);
					// assert elements_at_xpi_and_ypi_are_in_range(a, x, y, l);
					assert !elements_at_xpi_and_ypi_are_equal(a, x, y, l);
				}
			}
		}
		assert is_common_prefix_func(a[x..], a[y..], l);
		assert no_larger_common_prefix_exists_func(a[x..], a[y..], l) by {
			assert no_larger_common_prefix_exists(a, x, y, l);
			assert !exists ll: nat {:trigger} :: l < ll && is_common_prefix(a, x, y, ll);
			assert !exists ll: nat {:trigger} :: l < ll && is_common_prefix_func(a[x..], a[y..], ll) by {
				if exists ll: nat {:trigger} :: l < ll && is_common_prefix_func(a[x..], a[y..], ll) {
					var ll: nat :| l < ll && is_common_prefix_func(a[x..], a[y..], ll);
					assert !is_common_prefix(a, x, y, ll);
					assert is_common_prefix_func(a[x..], a[y..], ll);
					assert is_common_prefix(a, x, y, ll) by {
						forall i: nat | i < ll
							ensures elements_at_xpi_and_ypi_are_in_range(a, x, y, i) && elements_at_xpi_and_ypi_are_equal(a, x, y, i)
						{
							assert elements_at_i_are_in_range(a[x..], a[y..], i) && elements_at_i_are_equal(a[x..], a[y..], i);
							assert (i < |a[x..]| && i < |a[y..]| && a[x..][i] == a[y..][i]);
							// assert (i < a.Length - x && i < a.Length - y && a[x + i] == a[y + i]);
						}
						assert forall i: nat {:trigger} :: i < ll ==> elements_at_i_are_in_range(a[x..], a[y..], i) && elements_at_i_are_equal(a[x..], a[y..], i);
					}
				}
			}
		}
	}
	method lcp(i: nat) returns (l: nat) // public
		requires suffixes.Length - 1 > i - 1 >= 0
		requires suffixes[i] <= a.Length && suffixes[i - 1] <= a.Length
		ensures suffixes[i] + l <= a.Length && suffixes[i - 1] + l <= a.Length
		ensures is_common_prefix(a, suffixes[i], suffixes[i - 1], l)
		ensures no_larger_common_prefix_exists(a, suffixes[i], suffixes[i - 1], l)
	{
		l := lcp_helper(suffixes[i], suffixes[i - 1]);
	}
	lemma contraposition_of_compare(x: nat, y: nat)
		requires x < a.Length
		requires y < a.Length
		ensures compare(x, y) == -compare(y, x)
	{
		if x != y {
			ghost var n: int := compare(x, y);
			ghost var r: int := compare(y, x);
			ghost var l: nat := lcp_helper_function(a[x..], a[y..]);
			assert l == lcp_helper_function(a[y..], a[x..]) by {
				assert is_common_prefix_func(a[y..], a[x..], l) by {
					forall i: nat {:trigger} | i < l
						ensures elements_at_i_are_in_range(a[y..], a[x..], i) && elements_at_i_are_equal(a[y..], a[x..], i)
					{
						assert elements_at_i_are_equal(a[x..], a[y..], i);
					}
				}
				assert no_larger_common_prefix_exists_func(a[y..], a[x..], l) by {
					assert !exists ll: nat {:trigger} :: l < ll && is_common_prefix_func(a[y..], a[x..], ll) by {
						if exists ll: nat {:trigger} :: l < ll && is_common_prefix_func(a[y..], a[x..], ll) {
							var ll :| l < ll && is_common_prefix_func(a[y..], a[x..], ll);
							assert !is_common_prefix_func(a[y..], a[x..], ll) by {
								assert exists cll: nat {:trigger} :: cll < ll && !(elements_at_i_are_in_range(a[y..], a[x..], cll) && elements_at_i_are_equal(a[y..], a[x..], cll)) by {
									assert !elements_at_i_are_in_range(a[y..], a[x..], l) || !elements_at_i_are_equal(a[y..], a[x..], l) by {
										assert !(elements_at_i_are_in_range(a[x..], a[y..], l) && elements_at_i_are_equal(a[x..], a[y..], l)) by {
											assert forall i: nat {:trigger} :: i < l ==> elements_at_i_are_in_range(a[x..], a[y..], i) && elements_at_i_are_equal(a[x..], a[y..], i) by {
												assert no_larger_common_prefix_exists_func(a[x..], a[y..], l);
											}
											assert exists i: nat {:trigger} :: i < l + 1 && !(elements_at_i_are_in_range(a[x..], a[y..], i) && elements_at_i_are_equal(a[x..], a[y..], i)) by {
												assert !is_common_prefix_func(a[x..], a[y..], l + 1);
											}
										}
									}
									assert l < ll;
								}
							}
						}
					}
				}
			}
			if x + l < a.Length && y + l < a.Length {} // reduces resource usage from 669k to 401k
		}
	}
	ghost predicate transitive(x: nat, y: nat, z: nat)
		requires x < a.Length
		requires y < a.Length
		requires z < a.Length
		reads a
	{(
		(compare(x, y) == 0 && compare(y, z) == 0 ==> compare(x, z) == 0)
			&&
		(compare(x, y) < 0 && compare(y, z) <= 0 ==> compare(x, z) < 0)
			&&
		(compare(x, y) <= 0 && compare(y, z) <= 0 ==> compare(x, z) <= 0)
			&&
		(compare(x, y) > 0 && compare(y, z) >= 0 ==> compare(x, z) > 0)
			&&
		(compare(x, y) >= 0 && compare(y, z) >= 0 ==> compare(x, z) >= 0)
	)}
	lemma transitivity_of_compare(x: nat, y: nat, z: nat)
		requires x < a.Length
		requires y < a.Length
		requires z < a.Length
		ensures transitive(x, y, z)
	{
		ghost var cxy: int := compare(x, y);
		ghost var lxy: int := lcp_helper_function(a[x..], a[y..]);
		ghost var cyz: int := compare(y, z);
		ghost var lyz: int := lcp_helper_function(a[y..], a[z..]);
		ghost var cxz: int := compare(x, z);
		ghost var lxz: int := lcp_helper_function(a[x..], a[z..]);
		if cxy < 0 && cyz <= 0 {
			assert cxz == -1 by {
				if cyz == -1 {
					// assert x != y && y + lxy < a.Length && ((x + lxy == a.Length && y < x) || (x + lxy < a.Length && a[x + lxy] < a[y + lxy]));
					// assert y != z && z + lyz < a.Length && ((y + lyz == a.Length && z < y) || (y + lyz < a.Length && a[y + lyz] < a[z + lyz]));
					assume false;
				}
			}
		} else if cxy > 0 && cyz >= 0 {
			assert cxz == 1 by {
				if cyz == 1 {
					assume false; // try to prove this later
				}
			}
		}
	}
	function compare(x: nat, y: nat): (s: int) // public
		requires x < a.Length
		requires y < a.Length
		reads a
		ensures x == y <==> s == 0
		ensures ghost var l := lcp_helper_function(a[x..], a[y..]); (
			((x != y && x + l == a.Length) ==> (y + l < a.Length && y < x && s == -1))
				&&
			((x != y && y + l == a.Length) ==> (x + l < a.Length && x < y && s ==  1))
				&&
			((x != y && x + l < a.Length && y + l < a.Length && a[x + l] < a[y + l]) ==> s == -1)
				&&
			((x != y && x + l < a.Length && y + l < a.Length && a[x + l] >= a[y + l]) ==> (a[x + l] > a[y + l] && s == 1))
				&&
			(s == -1 ==> (x != y && y + l < a.Length && ((x + l == a.Length && y < x) || (x + l < a.Length && a[x + l] < a[y + l]))))
				&&
			(s ==  1 ==> (x != y && x + l < a.Length && ((y + l == a.Length && x < y) || (y + l < a.Length && a[x + l] > a[y + l]))))
		)
	{
		if x == y then
			0
		else
			var l: nat := lcp_helper_function(a[x..], a[y..]);
			if x + l == a.Length then
				-1
			else if y + l == a.Length then
				1
			else if a[x + l] < a[y + l] then
				-1
			else // if a[x + l] > a[y + l] then
				assert a[x + l] > a[y + l] by {
					assert a[x + l] != a[y + l] by {
						if a[x + l] == a[y + l] {
							assert is_common_prefix_func(a[x..], a[y..], l + 1);
							assert !is_common_prefix_func(a[x..], a[y..], l + 1) by {
								assert no_larger_common_prefix_exists_func(a[x..], a[y..], l);
							}
						}
					}
				}
				1
	}

	// helper lemmas for sort (they are, in fact, needed)
		lemma join_sorted_sequences(a: seq<nat>, b: seq<nat>)
			requires indexes_in_a(a)
			requires indexes_in_a(b)
			requires is_sorted(a)
			requires is_sorted(b)
			requires |a| > 0 && |b| > 0 ==> compare(a[|a| - 1], b[0]) <= 0
			ensures is_sorted(a + b)
		{
			if |a| > 0 && |b| > 0 {
				ghost var i: nat := 0;
				while i < |b|
					invariant i <= |b|
					invariant indexes_in_a(a + b)
					invariant is_sorted(a + b[..i])
				{
					i := i + 1;
					assert is_sorted(a + b[..i]) by { // forall j: nat, k: nat {:trigger} :: j < k < |a + b[..i]| ==> compare((a + b[..i])[j], (a + b[..i])[k]) <= 0 by {
						assert forall j: nat, k: nat {:trigger} :: j < k < |a + b[..i]| - 1 ==> compare((a + b[..i])[j], (a + b[..i])[k]) <= 0 by {
							assert forall j: nat {:trigger} :: j < |a + b[..i]| - 1 ==> (a + b[..i])[j] == (a + b[..i - 1])[j];
						}
						forall j: nat {:trigger} | j < |a + b[..i]| - 1
							ensures compare((a + b[..i])[j], (a + b[..i])[|a + b[..i]| - 1]) <= 0
						{
							assert compare((a + b[..i])[|a + b[..i]| - 2], (a + b[..i])[|a + b[..i]| - 1]) <= 0;
							transitivity_of_compare((a + b[..i])[j], (a + b[..i])[|a + b[..i]| - 2], (a + b[..i])[|a + b[..i]| - 1]);
						}
					}
				}
				assert is_sorted(a + b[..|b|]);
				assert b == b[..|b|];
			}
		}

		static lemma same_multisets<T(!new)>(a: seq<T>, b: array<T>, j: nat)
			requires |a| == b.Length
			requires 0 < j < b.Length
			requires a[..j - 1] == b[..j - 1]
			requires a[j - 1] == b[j]
			requires a[j] == b[j - 1]
			requires a[j + 1..] == b[j + 1..]
			ensures multiset(a) == multiset(b[..])
		{
			assert multiset(a[..j - 1] + [a[j - 1]] + [a[j]] + a[j + 1..])
					== multiset(b[..j - 1] + [b[j - 1]] + [b[j]] + b[j + 1..]) by {
				assert multiset(a[..j - 1]) + multiset([a[j - 1]]) + multiset([a[j]]) + multiset(a[j + 1..])
						== multiset(b[..j - 1]) + multiset([b[j - 1]]) + multiset([b[j]]) + multiset(b[j + 1..]) by {
					assert multiset(a[..j - 1]) == multiset(b[..j - 1]);
					assert multiset([a[j - 1]]) == multiset([b[j]    ]) by { assert [a[j - 1]] == [b[j]    ]; }
					assert multiset([a[j]    ]) == multiset([b[j - 1]]) by { assert [a[j]    ] == [b[j - 1]]; }
					assert multiset(a[j + 1..]) == multiset(b[j + 1..]);
				}
			}
			assert a     == a[..j - 1] + [a[j - 1]] + [a[j]] + a[j + 1..];
			assert b[..] == b[..j - 1] + [b[j - 1]] + [b[j]] + b[j + 1..];
		}

		static lemma is_still_reordering(before: seq<nat>, data: array<nat>, i: nat, j: nat, original_data: seq<nat>)
			requires |before| == data.Length == |original_data|
			requires 0 < j <= i
			requires 0 <= i < data.Length
			requires before[..j] == data[..j]
			requires before[j - 1] == data[j]
			requires before[j] == data[j - 1]
			requires before[j + 1..] == data[j + 1..]
			requires is_reordering_of(before, original_data)
			ensures is_reordering_of(data[..], original_data)
		{
			assert is_reordering_of(data[..], before) by {
				var p: seq<nat> := seq(|data[..]|, i => i);
				p := p[..j - 1] + [p[j]] + [p[j - 1]] + p[j + 1..];
			}
			transitivity_of_reordering(data[..], before, original_data);
		}

		lemma sorted_until_jm1(before: seq<nat>, data: array<nat>, j: nat)
			requires |before| == data.Length
			requires 0 < j <= data.Length
			requires indexes_in_a(before[..])
			requires is_sorted(before[..j])
			requires before[..j - 1] == data[..j - 1]
			ensures is_sorted(data[..j - 1])
		{}

		lemma j_separates_lower_from_greater(before: seq<nat>, data: array<nat>, i: nat, j: nat)
			requires |before| == data.Length
			requires 0 < j <= i
			requires 0 <= i < data.Length
			requires indexes_in_a(before[..])
			requires is_sorted(before[..j])
			requires before[..j - 1] == data[..j - 1]
			requires before[j - 1] == data[j]
			requires indexes_in_a(data[..])
			requires is_sorted(data[j - 1..i + 1])
			ensures index_separates_lower_from_greater(data[..i + 1], j - 1)
		{
			if 1 < j {
				forall k: nat, l: nat {:trigger} | k < j - 1 < l < |data[..i + 1]|
					ensures compare(data[..i + 1][k], data[..i + 1][l]) <= 0
				{
					assert compare(data[..i + 1][k], data[..i + 1][j]) <= 0 by {
						assert compare(data[..i + 1][k], data[..i + 1][j - 2]) <= 0 by {
							assert compare(data[..i + 1][..j - 1][k], data[..i + 1][..j - 1][j - 2]) <= 0 by {
								assert is_sorted(data[..i + 1][..j - 1]) by {
									assert is_sorted(data[..j - 1]) by {
										assert is_sorted(before[..j - 1]) by {
											assert is_sorted(before[..j][..j - 1]);
											assert before[..j - 1] == before[..j][..j - 1];
										}
									}
									assert data[..i + 1][..j - 1] == data[..j - 1];
								}
							}
						}
						assert compare(data[j - 2], data[j]) <= 0 by {
							assert compare(before[j - 2], before[j - 1]) <= 0 by {
								assert is_sorted(before[..j]);
								assert before[j - 1] == before[..j][j - 1];
								assert before[j - 2] == before[..j][j - 2];
							}
							assert data[j - 2] == before[j - 2] by {
								assert data[..j - 1] == before[..j - 1];
								assert data[j - 2] == data[..j - 1][j - 2];
								assert before[j - 2] == before[..j - 1][j - 2];
							}
							assert data[j] == before[j - 1];
						}
						transitivity_of_compare(data[..i + 1][k], data[..i + 1][j - 2], data[..i + 1][j]);
					}
					transitivity_of_compare(data[..i + 1][k], data[..i + 1][j], data[..i + 1][l]);
				}
			}
		}

		lemma sorted_from_jm1_to_ip1(before: seq<nat>, data: array<nat>, i: nat, j: nat) // verification is done 3 times faster by isolating assertions, but I've learned to not ask questions
			requires |before| == data.Length
			requires 0 < j <= i
			requires 0 <= i < data.Length
			requires jm1_to_j: before[j - 1] == data[j]
			requires j_to_jm1: before[j] == data[j - 1]
			requires unchanged_from_jp1: before[j + 1..] == data[j + 1..]
			requires indexes_in_a(before)
			requires until_j_lt_from_j_to_ip1: index_separates_lower_from_greater(before[..i + 1], j)
			requires sorted_from_j_to_ip1: is_sorted(before[j..i + 1])
			requires jm1_lt_j: compare(before[j - 1], before[j]) > 0
			requires indexes_in_a(data[..])
			ensures is_sorted(data[j - 1..i + 1])
		{
			assert is_sorted(data[j + 1..i + 1]) by {
				assert is_sorted(before[j + 1..i + 1]) by {
					assert is_sorted(before[j..i + 1][1..]) by {
						reveal sorted_from_j_to_ip1;

					}
					assert before[j + 1..i + 1] == before[j..i + 1][1..];
				}
				assert before[j + 1..i + 1] == data[j + 1..i + 1] by { reveal unchanged_from_jp1; }
			}
			assert is_sorted(data[j - 1..j + 1]) by {
				assert compare(data[j - 1], data[j]) <= 0 by {
					assert compare(data[j], data[j - 1]) > 0 by {
						reveal jm1_lt_j;
						reveal jm1_to_j;
						reveal j_to_jm1;
					}
					contraposition_of_compare(data[j], data[j - 1]);
				}
				assert data[j - 1..j + 1] == [data[j - 1], data[j]];
			}
			if j + 1 < i + 1 {
				assert compare(data[j - 1..j + 1][|data[j - 1..j + 1]| - 1], data[j + 1..i + 1][0]) <= 0 by {
					assert compare(data[j], data[j + 1]) <= 0 by {
						assert compare(before[j - 1], before[j + 1]) <= 0 by { reveal until_j_lt_from_j_to_ip1; }
						assert data[j] == before[j - 1] by { reveal jm1_to_j; }
						assert data[j + 1] == before[j + 1] by { reveal unchanged_from_jp1; }
					}
				}
				join_sorted_sequences(data[j - 1..j + 1], data[j + 1..i + 1]);
				assert data[j - 1..i + 1] == data[j - 1..j + 1] + data[j + 1..i + 1];
			}
		}

		lemma sorted_at_the_end(data: array<nat>, i: nat, j: nat)
			requires 0 <= j < i
			requires 0 <= i <= data.Length
			requires indexes_in_a(data[..])
			requires is_sorted(data[..j])
			requires is_sorted(data[j..i])
			requires j == 0 || compare(data[j - 1], data[j]) <= 0
			ensures is_sorted(data[..i])
		{
			if j > 0 {
				assert indexes_in_a(data[..]); // commenting this shoots the verifier in the head
				assert is_sorted(data[..j] + data[j..i]) by {
					assert is_sorted(data[..j]);
					assert is_sorted(data[j..i]);
					assert compare(data[..j][|data[..j]| - 1], data[j..i][0]) <= 0;
					join_sorted_sequences(data[..j], data[j..i]);
				}
				assert data[..i] == data[..j] + data[j..i];
			}
		}
	//
	ghost predicate indexes_in_a(s: seq<nat>)
	{forall i: nat {:trigger} :: i < |s| ==> s[i] < a.Length}

	ghost predicate is_sorted(s: seq<nat>)
		reads a
		requires indexes_in_a(s)
	{forall i: nat, j: nat {:trigger} :: i < j < |s| ==> compare(s[i], s[j]) <= 0}

	ghost predicate index_separates_lower_from_greater(s: seq<nat>, sep_idx: nat)
		requires sep_idx <= |s|
		reads a
		requires indexes_in_a(s)
	{forall i: nat, j: nat :: i < sep_idx < j < |s| ==> compare(s[i], s[j]) <= 0}

	method {:isolate_assertions} sort(data: array<nat>) // public // should be static?
		modifies data
		requires indexes_in_a(data[..])
		// ensures multiset(data[..]) == multiset(old(data[..]))
		ensures is_reordering_of(data[..], old(data[..]))
		ensures indexes_in_a(data[..])
		ensures is_sorted(data[..])
	{
		ghost var original_data: seq<nat> := data[..];
		var i := 0;
		assert is_reordering_of(data[..], original_data) by {
			var p: seq<nat> := seq(|data[..]|, i => i);
		}
		while i < data.Length
			invariant 0 <= i <= data.Length
			// invariant multiset(original_data) == multiset(data[..])
			invariant is_reordering_of(data[..], original_data)
			invariant indexes_in_a(data[..])
			invariant is_sorted(data[..i])
		{
			var j := i;
			while j > 0 && compare(data[j - 1], data[j]) > 0
				invariant i >= j >= 0
				invariant indexes_in_a(data[..])
				// invariant multiset(original_data) == multiset(data[..])
				invariant is_reordering_of(data[..], original_data)
				invariant is_sorted(data[..j])
				invariant index_separates_lower_from_greater(data[..i + 1], j)
				invariant is_sorted(data[j..i + 1])
			{
				ghost var before: seq<nat> := data[..];
				// assert elements_are_preserved_before_swap: multiset(original_data) == multiset(before);
				data[j - 1], data[j] := data[j], data[j - 1];

				assert before[..j - 1] == data[..j - 1];
				assert before[j + 1..] == data[j + 1..];
				assert before[j - 1] == data[j];
				assert before[j] == data[j - 1];

				// assert multiset(original_data) == multiset(data[..]) by {
				// 	same_multisets(before, data, j);
				// 	reveal elements_are_preserved_before_swap;
				// }
				assert {:only} is_reordering_of(data[..], original_data) by {
					assert is_reordering_of(data[..], before) by {
						// assume false;
						var p: seq<nat> := seq(|data[..]|, i => i);
						p := p[..j - 1] + [p[j]] + [p[j - 1]] + p[j + 1..];
						assert is_permutation_seq(p);
						assume false;
					}
					transitivity_of_reordering(data[..], before, original_data);
					// assume false;
				}
				// is_still_reordering(before, data, i, j, original_data) by { assert false; }
				sorted_until_jm1(before, data, j);
				sorted_from_jm1_to_ip1(before, data, i, j);
				j_separates_lower_from_greater(before, data, i, j);
				j := j - 1;
			}
			i := i + 1;
			sorted_at_the_end(data, i, j);
		}
		assert data[..] == data[..data.Length];
		// assert multiset(original_data) == multiset(data[..]);

		assert forall i: nat {:trigger} :: i < |data[..]| ==> data[..][i] < a.Length;
	}
	static method main(argv: seq<string>) // public
	{
		// var arr: seq<int> = [1,2,2,5];
		// SuffixArray sa = new SuffixArray(arr);
		// System.out.println(sa.lcp(1,2));
		// var brr: seq<int> = [1,2,3,5];
		// sa = new SuffixArray(brr);
		// System.out.println(sa.lcp(1,2));
		// var crr: seq<int> = [1,2,3,5];
		// sa = new SuffixArray(crr);
		// System.out.println(sa.lcp(2,3));
		// var drr: seq<int> = [1,2,3,3];
		// sa = new SuffixArray(drr);
		// System.out.println(sa.lcp(2,3));
	}
}
