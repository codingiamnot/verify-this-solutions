ghost predicate is_power_of_2(n: nat)
{n > 0 && (n == 1 || (exists nd2: nat {:trigger} :: nd2 < n && is_power_of_2(nd2) && n == nd2 * 2))}

ghost predicate is_2_to_the_power_of(n: nat, p: nat)
{is_power_of_2(n) && (p == 0 ==> n == 1) && (p > 0 ==> is_2_to_the_power_of(n / 2, p - 1))}

function log_of_power_of_2(n: nat) : (l: nat)
	requires is_power_of_2(n)
//
	ensures is_2_to_the_power_of(n, l)
{
	if n == 1 then
		0
	else
		1 + log_of_power_of_2(n / 2)
}

function two_to_the_power_of(p: nat) : (n: nat)
//
	ensures is_2_to_the_power_of(n, p)
{
	if p == 0 then
		1
	else
		2 * two_to_the_power_of(p - 1)
}

lemma {:induction false} exponent_logarithm_identity(a: nat)
	requires is_power_of_2(a)
//
	ensures a == two_to_the_power_of(log_of_power_of_2(a))
{
	if a > 1 {
		var ad2: nat :| ad2 < a && is_power_of_2(ad2) && a == ad2 * 2;
		exponent_logarithm_identity(ad2);
		var log_ad2: nat := log_of_power_of_2(ad2);
		var ad2': nat := two_to_the_power_of(log_ad2);
		calc == {
			a;
			ad2 * 2;
			ad2' * 2;
			two_to_the_power_of(log_ad2) * 2;
			two_to_the_power_of(1 + log_ad2 - 1) * 2;
			two_to_the_power_of(1 + log_ad2);
			{assert 1 + log_ad2 == log_of_power_of_2(a) by {
				assert log_of_power_of_2(ad2 * 2) == 1 + log_of_power_of_2(ad2) by {
					multiplication_then_division_cancel(ad2, 2);
				}
				assert ad2 * 2 == a;
			}}
			two_to_the_power_of(log_of_power_of_2(a));
		}
	}
}

lemma {:induction false} logarithm_exponent_identity(a: nat)
//
	ensures a == log_of_power_of_2(two_to_the_power_of(a))
{
	if a > 1 {
		var am1: nat := a - 1;
		logarithm_exponent_identity(am1);
		var two_pow_am1: nat := two_to_the_power_of(am1);
		var am1': nat := log_of_power_of_2(two_pow_am1);
		calc == {
			a;
			am1 + 1;
			am1' + 1;
			log_of_power_of_2(two_pow_am1) + 1;
			{ multiplication_then_division_cancel(two_pow_am1, 2); }
			log_of_power_of_2(two_pow_am1 * 2 / 2) + 1;
			log_of_power_of_2(two_pow_am1 * 2 / 2 * 2);
			{
				assert two_pow_am1 * 2 == two_pow_am1 * 2 / 2 * 2 + (two_pow_am1 * 2) % 2;
				assert (two_pow_am1 * 2) % 2 == 0 by {
					modulo_persists_while_steps_mul_by_y(0, two_pow_am1, 2);
				}
			}
			log_of_power_of_2(two_pow_am1 * 2);
			{assert two_pow_am1 * 2 == two_to_the_power_of(a) by {
				assert two_to_the_power_of(am1 + 1) == two_to_the_power_of(am1) * 2;
				// assert am1 + 1 == a;
			}}
			log_of_power_of_2(two_to_the_power_of(a));
		}
	}
}

lemma {:induction false} logarithmic_product_rule(a: nat, b: nat)
	requires a_is_power_of_2: is_power_of_2(a)
	requires b_is_power_of_2: is_power_of_2(b)
//
	ensures
		assert is_power_of_2(a * b) by { closure_under_multiplication_between_powers_of_2(a, b); }
		log_of_power_of_2(a * b) == log_of_power_of_2(a) + log_of_power_of_2(b)
{
	assert a_mul_b_is_power_of_2: is_power_of_2(a * b) by {
		closure_under_multiplication_between_powers_of_2(a, b) by {
			reveal a_is_power_of_2;
			reveal b_is_power_of_2;
		}
	}
	if a == 1 {
		assert log_of_power_of_2(a * b) == log_of_power_of_2(b) by {
			reveal a_mul_b_is_power_of_2;
			reveal b_is_power_of_2;
			assert a * b == b;
		}
		assert log_of_power_of_2(a) + log_of_power_of_2(b) == log_of_power_of_2(b) by {
			reveal a_is_power_of_2;
			reveal b_is_power_of_2;
			assert log_of_power_of_2(a) == 0;
		}
	} else {
		var ad2: nat :| ad2 < a && is_power_of_2(ad2) && a == ad2 * 2 by {
			reveal a_is_power_of_2;
		}
		assert log_of_power_of_2(a) == 2 * log_of_power_of_2(ad2);
		assume false;
	}
}

lemma {:induction false} idk(a: nat, b: nat)
//
	ensures two_to_the_power_of(a + b) == two_to_the_power_of(a) * two_to_the_power_of(b)

lemma strict_comparison_between_powers_of_2(a: nat, b: nat)
	requires is_power_of_2(a)
	requires is_power_of_2(b)
//
	ensures a < b <==> a <= b / 2
	ensures a > b <==> a >= b * 2
{}

lemma monotonicity_under_logarithmization_between_powers_of_2(a: nat, b: nat)
	requires is_power_of_2(a)
	requires is_power_of_2(b)
//
	ensures log_of_power_of_2(a) < log_of_power_of_2(b) ==> a <= b / 2
	ensures a < b ==> log_of_power_of_2(a) < log_of_power_of_2(b)
	ensures log_of_power_of_2(a) == log_of_power_of_2(b) <==> a == b
	ensures a > b ==> log_of_power_of_2(a) > log_of_power_of_2(b)
	ensures log_of_power_of_2(a) > log_of_power_of_2(b) ==> a >= b * 2
{}

lemma {:isolate_assertions} power_of_2_divides_bigger_power_of_2(a: nat, b: nat)
	requires a >= b
	requires is_power_of_2(a)
	requires is_power_of_2(b)
//
	ensures a % b == 0
{
	var ac: nat := a;
	var bc: nat := b;
	var p: nat := 1;
	while bc > 1
		invariant is_power_of_2(ac)
		invariant is_power_of_2(bc)
		invariant ac >= bc
		invariant a == ac * p
		invariant b == bc * p
	{
		ac := ac / 2;
		bc := bc / 2;
		p := p * 2;
	}
	assert bc == 1;
	// assert b == bc * p;
	// assert b == p;
	// assert a == ac * p;
	assert a == ac * b;
	assert (ac * b) % b == 0 by {
		var d: nat := (ac * b) / b;
		var r: nat := (ac * b) % b;
		// assert ac * b == d * b + r;
		var ac': nat := ac;
		var d': nat := d;
		while ac' > 0
			invariant ac' <= ac
			invariant ac' * b == d' * b + r
		{
			ac' := ac' - 1;
			d' := d' - 1;
		}
		// assert ac' == 0;
		// assert ac' * b == 0;
		// assert d' * b + r == 0;
		// assert d' == 0 && r == 0;
	}
}
lemma {:induction false} closure_under_division_between_powers_of_2(a: nat, b: nat)
	decreases a - b
	requires a_is_power_of_2: is_power_of_2(a)
	requires b_is_power_of_2: is_power_of_2(b)
	requires a_ge_b: a >= b
//
	ensures is_power_of_2(a / b)
{
	var acpm_t: (nat, nat, nat) -> bool := (a, b, c) => true;
	assert forall a: nat, b: nat, c: nat {:trigger acpm_t(a, b, c)} :: a * (b * c) == a * c * b;
	var a': nat := a;
	assert is_power_of_2(a') by { reveal a_is_power_of_2; }
	var b': nat := b;
	assert is_power_of_2(b') by { reveal b_is_power_of_2; }
	assert a' >= b' by { reveal a_ge_b; }
	var factor: nat := 1;
	while b' != 1
		decreases b'
		invariant is_power_of_2(a')
		invariant is_power_of_2(b')
		invariant a' >= b'
		invariant a == a' * factor
		invariant b == b' * factor
		invariant is_power_of_2(factor)
	{
  	var a'd2: nat :| a'd2 < a' && is_power_of_2(a'd2) && a' == a'd2 * 2;
		assert a == a'd2 * (factor * 2) by {
			calc == {
				a'd2 * (factor * 2);
				a'd2 * 2 * factor;
				{ assert acpm_t(a'd2, factor, 2); }
				a' * factor;
			}
		}
		var b'd2: nat :| b'd2 < b' && is_power_of_2(b'd2) && b' == b'd2 * 2;
		assert b == b'd2 * (factor * 2) by {
			calc == {
				b'd2 * (factor * 2);
				b'd2 * 2 * factor;
				{ assert acpm_t(b'd2, factor, 2); }
				b' * factor;
			}
		}
		a' := a'd2;
		b' := b'd2;
		factor := factor * 2;
	}
	assert {:focus} a / b == a' by {
		assert a / b == a' * b / b by {
			assert a == a' * b by {
				assert b == factor;
			}
		}
		multiplication_then_division_cancel(a', b);
	}
}

lemma {:induction false} closure_under_multiplication_between_powers_of_2(a: nat, b: nat)
	requires a_is_power_of_2: is_power_of_2(a)
	requires b_is_power_of_2: is_power_of_2(b)
//
	ensures is_power_of_2(a * b)
{
	if a == 1 {
		assert a * b == b;
		reveal b_is_power_of_2;
	} else {
		var ad2: nat :| ad2 < a && is_power_of_2(ad2) && a == ad2 * 2 by {
			reveal a_is_power_of_2;
		}
		closure_under_multiplication_between_powers_of_2(ad2, 2 * b) by {
			assert is_power_of_2(2 * b) by {
				reveal b_is_power_of_2;
			}
		}
		calc == {
			a * b;
			ad2 * 2 * b;
			ad2 * (2 * b);
		}
	}
}

function sum(a: seq<int>): (s: int)
{if |a| == 0 then 0 else a[0] + sum(a[1..])}

lemma {:induction false} additivity_of_sum_over_consecutive_slices_seq(a: seq<int>, start: nat, mid: nat, end: nat)
	requires start <= mid <= end <= |a|
//
	ensures sum(a[start..end]) == sum(a[start..mid]) + sum(a[mid..end])
{
	assert a[start..end] == a[start..mid] + a[mid..end];
	additivity_of_sum(a[start..mid], a[mid..end]);
}

lemma {:induction false} additivity_of_sum(a: seq<int>, b: seq<int>)
	decreases |a|, |b|
//
	ensures sum(a + b) == sum(a) + sum(b)
{
	if |a| > 0 {
		assert sum(a + b) == a[0] + sum(a[1..]) + sum(b) by {
			assert sum(a + b) == (a + b)[0] + sum(a[1..]) + sum(b) by {
				assert sum(a + b) == (a + b)[0] + sum(a[1..] + b) by {
					// assert sum(a + b) == (a + b)[0] + sum((a + b)[1..]); // it's quicker if you let the prover take this step on its own
					assert a[1..] + b == (a + b)[1..];
				}
				assert sum(a[1..] + b) == sum(a[1..]) + sum(b) by {
					additivity_of_sum(a[1..], b);
				}
			}
			assert (a + b)[0] == a[0];
		}
	} else {
		calc == {
			sum([] + b);
			{ assert [] + b == b; }
			sum(b);
			0 + sum(b);
			sum([]) + sum(b);
		}
	}
}

lemma {:induction false} modulo_persists_while_steps_mul_by_y(x: int, y: int, z: nat)
	requires z > 0
//
	ensures (x + y * z) % z == x % z
{
	var d: int := (x + y * z) / z;
	var r: nat := (x + y * z) % z;
	var xd: int := x / z;
	var xr: nat := x % z;
	assert x == xd * z + xr;
	assert x + y * z == (xd + y) * z + xr;
	var cd: int := xd + y;
	var d': int := d;
	var cd': int := cd;
	if d' > 0 {
		while d' > 0
			invariant 0 <= d' <= d
			invariant d' * z + r == cd' * z + xr
		{
			d' := d' - 1;
			cd' := cd' - 1;
		}
	} else {
		while d' < 0
			invariant d <= d' <= 0
			invariant d' * z + r == cd' * z + xr
		{
			d' := d' + 1;
			cd' := cd' + 1;
		}
	}
	assert d' * z + r == cd' * z + xr;
	assert d' == 0;
	assert r == xr by {
		assert r == cd' * z + xr by {
			assert d' == 0;
			assert d' * z == 0;
			assert d' * z + r == r;
		}
		assert cd' == 0 by {
			if cd' >= 1 {
				assert cd' * z >= z;
				assert cd' * z + xr >= z;
				assert r >= z;
				assert false;
			}
			if cd' <= -1 {
				assert cd' * z + xr < 0 by {
					assert cd' * z <= -z;
					assert cd' * z + xr <= -z + xr;
					assert xr < z;
					assert -z + xr < -z + z;
				}
				assert r < 0;
				assert false;
			}
		}
	}
}

lemma {:induction false} monotonicity_under_plain_multiplication(a: int, b: int, c: int)
	requires c > 0
//
	ensures a < b <==> a * c < b * c
	ensures a == b <==> a * c == b * c
	ensures a > b <==> a * c > b * c
{}

lemma {:induction false} monotonicity_under_plain_division(a: int, b: int, c: int)
	requires c > 0
//
	ensures a - a % c < b - b % c <==> a / c < b / c
	ensures a == b ==> a / c == b / c
	ensures a / c == b / c ==> a - a % c == b - b % c
	ensures a - a % c > b - b % c <==> a / c > b / c
{}

lemma {:induction false} multiplicative_inverse_property_between_powers_of_2(a: nat, b: nat)
	requires is_power_of_2(a)
	requires is_power_of_2(b)
	requires a >= b
//
	ensures a / b * b == a
{
	assert a == a / b * b + a % b;
	assert a % b == 0 by {
		power_of_2_divides_bigger_power_of_2(a, b);
	}
}

lemma {:induction false} multiplication_then_division_cancel(a: int, b: int)
	requires b > 0
//
	ensures a * b / b == a
{
	assert (a * b) % b == 0 by {
		modulo_persists_while_steps_mul_by_y(0, a, b);
	}
}

// upsweep_iter helper functions
	ghost predicate last_position_is_sum_of_old_elements_rec(original_elements: seq<int>, a: seq<int>, lower_bound: nat, space: nat)
		decreases space
		requires |original_elements| == |a|
		requires is_power_of_2(space)
		requires is_power_of_2(|a|)
		requires lower_bound + space * 2 <= |a|
	{
		a[lower_bound + space - 1] == sum(original_elements[lower_bound..lower_bound + space])
		&&
		(space > 1 ==> (
			var spaced2: nat :| spaced2 < space && is_power_of_2(spaced2) && space == spaced2 * 2;
			last_position_is_sum_of_old_elements_rec(original_elements, a, lower_bound, spaced2)
			&&
			last_position_is_sum_of_old_elements_rec(original_elements, a, lower_bound + space, spaced2)
		))
	}

	lemma section_end_within_bounds(a: seq<int>, start: nat, space: nat)
		requires is_power_of_2(space)
		requires is_power_of_2(|a|)
		requires start < |a| / space
	//
		ensures start * space + space <= |a|
	{
		monotonicity_under_plain_multiplication(start, |a| / space - 1, space);
		multiplicative_inverse_property_between_powers_of_2(|a|, space);
	}

	ghost predicate last_position_is_sum_of_old_elements(original_elements: seq<int>, a: seq<int>, start: nat, space: nat)
		requires |original_elements| == |a|
		requires is_power_of_2(space)
		requires is_power_of_2(|a|)
		requires start < |a| / space
	{
		section_end_within_bounds(a, start, space);
		a[start * space + space - 1] == sum(original_elements[start * space..start * space + space])
		&&
		(space > 1 ==> (
			var spaced2: nat :| spaced2 < space && is_power_of_2(spaced2) && space == spaced2 * 2;
			assert start * space + spaced2 * 2 <= |a|;
			last_position_is_sum_of_old_elements_rec(original_elements, a, start * space, spaced2)
		))
	}

	lemma {:induction false} if_last_pos_is_sum_of_old_elements_for_a_then_it_is_for_b_with_equal_sequence(original_elements: seq<int>, a: seq<int>, b: seq<int>, start: nat, space: nat)
		requires |original_elements| == |a| == |b|
		requires is_power_of_2(space)
		requires is_power_of_2(|a|)
		requires start < |a| / space
		requires
			assert start * space + space <= |a| by { section_end_within_bounds(a, start, space); }
			last_position_is_sum_of_old_elements(original_elements, a, start, space)
		requires a[start * space..start * space + space] == b[start * space..start * space + space]
	//
		ensures last_position_is_sum_of_old_elements(original_elements, b, start, space)
	{
		if space > 1 {

			assume false;
		}
	}

	ghost predicate sums_s_to_s_until_n_are_computed(original_elements: seq<int>, a: seq<int>, space: nat, lower_bound: nat, upper_bound: nat)
		requires |original_elements| == |a|
		requires is_power_of_2(space)
		requires is_power_of_2(|a|)
		requires upper_bound <= |a| / space
	{
		(forall start: nat {:trigger} :: lower_bound <= start < upper_bound ==>
			last_position_is_sum_of_old_elements(original_elements, a, start, space))
		// &&
		// (space > 1 ==>
		// var space_div_2: nat :| space_div_2 < space && is_power_of_2(space_div_2) && space == space_div_2 * 2;
		// upper_bound_within_bounds_for_usbsequent_iterations(a, upper_bound, space_div_2);
		// sums_s_to_s_until_n_are_computed(original_elements, a, space_div_2, lower_bound * 2, upper_bound * 2, false))
	}
	
	//
		// s: 8, 3 <= start < 6 => 3, 4, 5 => [24..32], [32..40], [40..48] => 3, 4, 5
		// s: 4, 6 <= start < 12 => 6, 7, 8, 9, 10, 11 =>
		//			[24..28], [28..32], [32..36], [36..40], [40..44], [44..48] =>
		//			[24..28], [32..36], [40..44] => 6, 8, 10
		// s: 2, 12 <= start < 24 => 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23 =>
		//			[24..26], [26..28], [28..30], [30..32], [32..34], [34..36],
		//			[36..38], [38..40], [40..42], [42..44], [44..46], [46..48] =>
		//			[24..26], [28..30], [32..34], [36..38], [40..42], [44..46] => 12, 14, 16, 18, 20, 22
		// s:1, 24 <= start < 48 => 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
		//													36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47 =>
		//			[24..25], [25..26], [26..27], [27..28], [28..29], [29..30], [30..31], [31..32],
		//			[32..33], [33..34], [34..35], [35..36], [36..37], [37..38], [38..39], [39..40],
		//			[40..41], [41..42], [42..43], [43..44], [44..45], [45..46], [46..47], [47..48] =>
		//			[24..25], [26..27], [28..29], [30..31], [32..33], [34..35],
		//			[36..37], [38..39], [40..41], [42..43], [44..45], [46..47] =>
		//			24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46

	lemma sums_of_1_are_computed_at_the_beginning(original_elements: seq<int>, a: array<int>)
		requires original_elements == a[..]
		requires is_power_of_2(a.Length)
	//
		ensures sums_s_to_s_until_n_are_computed(original_elements, a[..], 1, 0, a.Length)
	{
	  forall start: nat {:trigger} | 0 <= start < a.Length
			ensures last_position_is_sum_of_old_elements(original_elements, a[..], start, 1)
		{}
	}

	lemma {:induction false} sums_s_to_s_are_computed(original_elements: seq<int>, a: array<int>, space: nat, lub: nat)
		requires |original_elements| == a.Length
		requires is_power_of_2(space)
		requires is_power_of_2(a.Length)
		requires lub <= a.Length / space
	//
		ensures sums_s_to_s_until_n_are_computed(original_elements, a[..], space, lub, lub)
	{}

	lemma {:induction false} RAW_acc_bounds_within_loop(left: nat, acc: nat, a: array<int>, space: nat)
		requires left == acc * space * 2 + space - 1
		requires left < a.Length
		requires a.Length % (space * 2) == 0
	//
		ensures acc <= a.Length / (space * 2) - 1
	{
		// assert acc < a.Length / (space * 2) by {
		// 	assert acc + (space - 1) / (space * 2) < a.Length / (space * 2) by {
		// 		assert acc * space * 2 + space - 1 < a.Length;
		// 	}
		// }
	}
	lemma {:induction false} acc_bounds_within_loop(left: nat, acc: nat, a: array<int>, space: nat)
		requires left_wrt_acc: left == acc * space * 2 + space - 1
		requires left_within_bounds: left < a.Length
		requires len_is_power_of_2: is_power_of_2(a.Length)
		requires space_mul_2_is_power_of_2: is_power_of_2(space * 2)
		requires space_mul_2_le_len: space * 2 <= a.Length
	//
		ensures acc <= a.Length / (space * 2) - 1
		ensures acc * space <= a.Length / 2 - space
		ensures acc * 2 <= a.Length / space - 2
		ensures acc * space * 2 <= a.Length - space * 2
	{
		assert space_mul_2_gt_0: (space * 2) > 0 by {
			reveal space_mul_2_is_power_of_2;
		}
		assert first_acc_bound: acc <= a.Length / (space * 2) - 1 by {
			reveal space_mul_2_gt_0;
			RAW_acc_bounds_within_loop(left, acc, a, space) by {
				assert a.Length % (space * 2) == 0 by {
					power_of_2_divides_bigger_power_of_2(a.Length, space * 2) by {
						reveal len_is_power_of_2;
						reveal space_mul_2_is_power_of_2;
						reveal space_mul_2_le_len;
					}
				}
				reveal left_wrt_acc;
				reveal left_within_bounds;
			}
		}
		assert fourth_acc_bound: acc * space * 2 <= a.Length - space * 2 by {
			assert acc * (space * 2) <= (a.Length / (space * 2) - 1) * (space * 2) by {
				monotonicity_under_plain_multiplication(acc, a.Length / (space * 2) - 1, space * 2) by {
					reveal space_mul_2_le_len;
				}
				reveal first_acc_bound;
			}
			calc == {
				(a.Length / (space * 2) - 1) * (space * 2);
				a.Length / (space * 2) * (space * 2) - space * 2;
				{
					multiplicative_inverse_property_between_powers_of_2(a.Length, space * 2) by {
						reveal len_is_power_of_2;
						reveal space_mul_2_is_power_of_2;
						reveal space_mul_2_le_len;
					}
				}
				a.Length - space * 2;
			}
			assert acc * space * 2 == acc * (space * 2) by {
				var t: (nat, nat, nat) -> bool := (a, b, c) => true;
				assert forall a: nat, b: nat, c: nat {:trigger t(a, b, c)} :: a * b * c == a * (b * c);
				assert t(acc, space, 2);
			}
		}
		assert second_acc_bound: acc * space <= a.Length / 2 - space by {
			assert (acc * space * 2) / 2 <= (a.Length - space * 2) / 2 by {
				reveal fourth_acc_bound;
				monotonicity_under_plain_division(acc * space * 2, a.Length - space * 2, 2);
			}
		}
		assert third_acc_bound: acc * 2 <= a.Length / space - 2 by {
			assert (acc * space * 2) / space <= (a.Length - space * 2) / space by {
				reveal fourth_acc_bound;
				assert (acc * space * 2) % space == 0 by {
					assert acc * space * 2 == (acc * 2) * space;
					modulo_persists_while_steps_mul_by_y(0, acc * 2, space);
				}
				assert (a.Length - space * 2) % space == 0 by {
					modulo_persists_while_steps_mul_by_y(a.Length, -2, space);
					assert a.Length % space == 0 by {
						power_of_2_divides_bigger_power_of_2(a.Length, space) by {
							reveal len_is_power_of_2;
							reveal space_mul_2_is_power_of_2;
						}
					}
				}
				monotonicity_under_plain_division(acc * space * 2, a.Length - space * 2, space);
			}
			assert (acc * space * 2) / space == acc * 2 by {
				multiplication_then_division_cancel(acc * 2, space);
				assert (acc * space * 2) / space == (acc * 2) * space / space;
			}
			assert (a.Length - space * 2) / space == a.Length / space - 2 by {
				calc == {
					(a.Length - space * 2) / space;
					{
						var t: (nat, nat, nat) -> bool := (a, b, c) => true;
						forall a: nat, b: nat, c: nat {:trigger t(a, b, c)} | c > 0 && a % c == 0 && b % c == 0
							ensures (a - b) / c == a / c - b / c
						{
							assert (a / c * c - b / c * c) / c == a / c - b / c by {
								assert (a / c * c - b / c * c) == (a / c - b / c) * c;
								multiplication_then_division_cancel(a / c - b / c, c);
							}
							assert a == a / c * c;
							assert b == b / c * c;
						}
						reveal len_is_power_of_2;
						reveal space_mul_2_is_power_of_2;
						power_of_2_divides_bigger_power_of_2(a.Length, space);
						power_of_2_divides_bigger_power_of_2(space * 2, space);
						assert t(a.Length, space * 2, space);
					}
					a.Length / space - (space * 2) / space;
					{ multiplication_then_division_cancel(2, space); }
					a.Length / space - 2;
				}
			}
		}
		reveal first_acc_bound;
		reveal second_acc_bound;
		reveal third_acc_bound;
		reveal fourth_acc_bound;
	}

	lemma {:induction false} left_bounds_within_loop(left: nat, acc: nat, a: array<int>, space: nat)
		requires left_wrt_acc: left == acc * space * 2 + space - 1
		requires left_within_bounds: left < a.Length
		requires len_is_power_of_2: is_power_of_2(a.Length)
		requires space_mul_2_is_power_of_2: is_power_of_2(space * 2)
		requires space_mul_2_le_len: space * 2 <= a.Length
	//
		ensures left <= a.Length - space - 1
	{
		assert acc * space * 2 + space - 1 <= a.Length - space - 1 by {
			assert acc * space * 2 <= a.Length - space * 2 by {
				assert space * 2 > 0 by {
					reveal space_mul_2_is_power_of_2;
				}
				assert acc <= a.Length / (space * 2) - 1 by {
					acc_bounds_within_loop(left, acc, a, space) by {
						reveal left_wrt_acc;
						reveal left_within_bounds;
						reveal len_is_power_of_2;
						reveal space_mul_2_is_power_of_2;
						reveal space_mul_2_le_len;
					}
				}
				monotonicity_under_plain_multiplication(acc, a.Length / (space * 2) - 1, space * 2);
				multiplicative_inverse_property_between_powers_of_2(a.Length, space * 2) by {
					reveal len_is_power_of_2;
					reveal space_mul_2_is_power_of_2;
					reveal space_mul_2_le_len;
				}
			}
		}
		reveal left_wrt_acc;
	}


	lemma {:induction false} if_equal_for_slice_then_equal_for_subslice(a: seq<int>, b: array<int>, lb: nat, ilb: nat, iub: nat, ub: nat)
		requires |a| == b.Length
		requires 0 <= lb <= ilb <= iub <= ub <= |a|
		requires a[lb..ub] == b[lb..ub]
	//
		ensures a[ilb..iub] == b[ilb..iub]
	{
		forall i: nat {:trigger} | ilb <= i < iub
			ensures a[i] == b[i]
		{}
	}

	lemma {:induction false} calculated_sums_for_currect_iteration(original_elements: seq<int>, before: seq<int>, a: array<int>, space: nat, acc: nat)
		requires lengths_are_equal: |original_elements| == |before| == a.Length
		requires space_is_power_of_2: is_power_of_2(space)
		requires len_is_power_of_2: is_power_of_2(a.Length)
		requires space_le_len: space <= a.Length
		requires first_acc_bound: acc <= a.Length / space - 1
		requires computed_until_acc: sums_s_to_s_until_n_are_computed(original_elements, before, space, 0, acc)
		requires unchanged_until_acc_times_space: before[..acc * space] == a[..acc * space]
		requires last_position_is_sum_of_old_elements(original_elements, a[..], acc, space)
	//
		ensures sums_s_to_s_until_n_are_computed(original_elements, a[..], space, 0, acc + 1)
	{
		assert space_gt_0: space > 0 by {
			reveal space_is_power_of_2;
		}
		forall start: nat {:trigger} | 0 <= start < acc + 1
			ensures
				reveal lengths_are_equal;
				reveal first_acc_bound;
				reveal space_is_power_of_2;
				reveal len_is_power_of_2;
				reveal space_le_len;
				last_position_is_sum_of_old_elements(original_elements, a[..], start, space)
		{
			if start < acc {
				assert start_bounds: start <= acc - 1;
				assert start_precondition: start < a.Length / space by {
					reveal space_gt_0;
					assert start <= a.Length / space - 2 by {
						reveal start_bounds;
						reveal first_acc_bound;
					}
				}
				assert sums_calculated_for_start_in_before: last_position_is_sum_of_old_elements(original_elements, before, start, space) by {
					reveal lengths_are_equal;
					reveal first_acc_bound;
					reveal space_is_power_of_2;
					reveal len_is_power_of_2;
					reveal space_le_len;
					reveal computed_until_acc;
				}
				if_last_pos_is_sum_of_old_elements_for_a_then_it_is_for_b_with_equal_sequence(original_elements, before, a[..], start, space) by {
					reveal lengths_are_equal;
					reveal space_is_power_of_2;
					reveal len_is_power_of_2;
					reveal start_precondition;
					reveal sums_calculated_for_start_in_before;
					if_equal_for_slice_then_equal_for_subslice(before, a, 0, start * space, start * space + space, acc * space) by {
						assert 0 <= start * space;
						assert start * space <= start * space + space;
						assert start * space + space <= acc * space by {
							assert start + 1 <= acc by {
								reveal start_bounds;
							}
							monotonicity_under_plain_multiplication(start + 1, acc, space);
							assert (start + 1) * space == start * space + space;
						}
						assert acc * space <= a.Length by {
							assert acc <= a.Length / space by {
								reveal first_acc_bound;
							}
							monotonicity_under_plain_multiplication(acc, a.Length / space, space);
							multiplicative_inverse_property_between_powers_of_2(a.Length, space) by {
								reveal len_is_power_of_2;
								reveal space_is_power_of_2;
								reveal space_le_len;
							}
						}
						reveal unchanged_until_acc_times_space;
					}
				}
			}
		}
	}

	lemma {:induction false} rest_of_previous_sums_are_kept(original_elements: seq<int>, before: seq<int>, a: array<int>, space: nat, acc: nat)
		requires lengths_are_equal: |original_elements| == |before| == a.Length
		requires space_mul_2_is_power_of_2: is_power_of_2(space * 2)
		requires len_is_power_of_2: is_power_of_2(a.Length)
		requires space_mul_2_le_len: space * 2 <= a.Length
		requires first_acc_bound: acc <= a.Length / (space * 2) - 1
		requires third_acc_bound: acc * 2 <= a.Length / space - 2
		requires fourth_acc_bound: acc * space * 2 <= a.Length - space * 2
		requires computed_from_acc_mul_2: sums_s_to_s_until_n_are_computed(original_elements, before, space, acc * 2, a.Length / space)
		requires unchanged_from_acc_plus_1_times_2_times_space: before[(acc + 1) * 2 * space..] == a[(acc + 1) * 2 * space..]
	//
		ensures sums_s_to_s_until_n_are_computed(original_elements, a[..], space, (acc + 1) * 2, a.Length / space)
	{
		assert space_is_power_of_2: is_power_of_2(space) by {
			reveal space_mul_2_is_power_of_2;
		}
		assert space_gt_0: space > 0 by {
			reveal space_is_power_of_2;
		}
		assert space_lt_len: space < a.Length by {
			reveal space_mul_2_le_len;
			reveal space_gt_0;
		}
		forall start: nat {:trigger} | (acc + 1) * 2 <= start < reveal space_gt_0; a.Length / space
			ensures
				reveal lengths_are_equal;
				reveal space_is_power_of_2;
				reveal len_is_power_of_2;
				last_position_is_sum_of_old_elements(original_elements, a[..], start, space)
		{
			assert start_bounds: start <= a.Length / space - 1;
			assert sums_calculated_for_start_in_before: last_position_is_sum_of_old_elements(original_elements, before, start, space) by {
				reveal lengths_are_equal;
				reveal space_is_power_of_2;
				reveal len_is_power_of_2;
				reveal space_lt_len;
				reveal computed_from_acc_mul_2;
			}
			if_last_pos_is_sum_of_old_elements_for_a_then_it_is_for_b_with_equal_sequence(original_elements, before, a[..], start, space) by {
				reveal lengths_are_equal;
				reveal space_is_power_of_2;
				reveal len_is_power_of_2;
				reveal start_bounds;
				reveal sums_calculated_for_start_in_before;
				if_equal_for_slice_then_equal_for_subslice(before, a, (acc + 1) * 2 * space, start * space, start * space + space, a.Length) by {
					assert (acc + 1) * 2 * space <= start * space by {
						assert (acc + 1) * 2 <= start;
						monotonicity_under_plain_multiplication((acc + 1) * 2, start, space);
					}
					assert start * space + space <= a.Length by {
						assert start * space + space <= a.Length / space * space by {
							assert (start + 1) * space <= a.Length / space * space by {
								assert start + 1 <= a.Length / space;
								monotonicity_under_plain_multiplication(start + 1, a.Length / space, space);
							}
							assert (start + 1) * space == start * space + space;
						}
						multiplicative_inverse_property_between_powers_of_2(a.Length, space) by {
							reveal len_is_power_of_2;
							reveal space_is_power_of_2;
							reveal space_lt_len;
						}
					}
					reveal unchanged_from_acc_plus_1_times_2_times_space;
				}
			}
		}
	}
	lemma {:induction false} array_change_resulted_in_next_sum(original_elements: seq<int>, before: seq<int>, a: array<int>, space: nat, acc: nat)
		requires lengths_are_equal: |original_elements| == |before| == a.Length
		requires space_is_power_of_2: is_power_of_2(space)
		requires len_is_power_of_2: is_power_of_2(a.Length)
		requires space_mul_2_le_len: space * 2 <= a.Length
		requires first_acc_bound: acc <= a.Length / (space * 2) - 1
		requires third_acc_bound: acc * 2 <= a.Length / space - 2
		requires fourth_acc_bound: acc * space * 2 <= a.Length - space * 2

		requires unchanged_from_acc_space_2_to_new_sum_exclusive: a[acc * space * 2..acc * space * 2 + space * 2 - 1] == before[acc * space * 2..acc * space * 2 + space * 2 - 1]
		requires new_sum: a[acc * space * 2 + space * 2 - 1] == before[acc * space * 2 + space - 1] + before[acc * space * 2 + space * 2 - 1]

		requires left_half_sum: last_position_is_sum_of_old_elements(original_elements, before, acc * 2, space)
		requires right_half_sum: last_position_is_sum_of_old_elements(original_elements, before, acc * 2 + 1, space)
	//
		ensures last_position_is_sum_of_old_elements(original_elements, a[..], acc, space * 2)
	{
		assert 0 <= acc * (space * 2) <= acc * (space * 2) + space * 2 <= a.Length by {
			reveal fourth_acc_bound;
		}
		assert a[acc * (space * 2) + space * 2 - 1] == sum(original_elements[acc * (space * 2)..acc * (space * 2) + space * 2]) by {
			assert before[acc * (space * 2) + space - 1] == sum(original_elements[acc * (space * 2)..acc * (space * 2) + space]) by {
				assert acc * (space * 2) == (acc * 2) * space;
				assert before[(acc * 2) * space + space - 1] == sum(original_elements[(acc * 2) * space..(acc * 2) * space + space]) by {
					reveal lengths_are_equal;
					reveal space_is_power_of_2;
					reveal len_is_power_of_2;
					reveal third_acc_bound;
					reveal left_half_sum;
				}
			}
			assert before[acc * (space * 2) + space * 2 - 1] == sum(original_elements[acc * (space * 2) + space..acc * (space * 2) + space * 2]) by {
				assert acc * space * 2 + space == acc * (space * 2) + space == (acc * 2 + 1) * space;
				assert 0 <= (acc * 2 + 1) * space <= (acc * 2 + 1) * space + space <= a.Length;
				assert before[(acc * 2 + 1) * space + space - 1] == sum(original_elements[(acc * 2 + 1) * space..(acc * 2 + 1) * space + space]) by {
					reveal lengths_are_equal;
					reveal space_is_power_of_2;
					reveal len_is_power_of_2;
					reveal third_acc_bound;
					reveal right_half_sum;
				}
			}
			additivity_of_sum_over_consecutive_slices_seq(original_elements, acc * (space * 2), acc * (space * 2) + space, acc * (space * 2) + space * 2);
			assert acc * (space * 2) == acc * space * 2 by {
				assert forall a: nat, b: nat, c: nat {:trigger} :: a * (b * c) == a * b * c;
			}
			reveal new_sum;
		}
		assert last_position_is_sum_of_old_elements_rec(original_elements, a[..], acc * (space * 2), space) by {
			reveal lengths_are_equal;
			reveal len_is_power_of_2;
			reveal space_is_power_of_2;
			assert a[acc * (space * 2) + space - 1] == sum(original_elements[acc * (space * 2)..acc * (space * 2) + space]) by {
				assert before[(acc * 2) * space + space - 1] == sum(original_elements[(acc * 2) * space..(acc * 2) * space + space]) by {
					reveal lengths_are_equal;
					reveal space_is_power_of_2;
					reveal len_is_power_of_2;
					reveal third_acc_bound;
					reveal left_half_sum;
				}
				assert a[acc * (space * 2) + space - 1] == before[(acc * 2) * space + space - 1] by {
					reveal unchanged_from_acc_space_2_to_new_sum_exclusive;
				}
			}
			if space > 1 {
				var spaced2: nat :| spaced2 < space && is_power_of_2(spaced2) && space == spaced2 * 2;
				assume {:axiom} last_position_is_sum_of_old_elements_rec(original_elements, a[..], acc * (space * 2), spaced2);
				assume {:axiom} last_position_is_sum_of_old_elements_rec(original_elements, a[..], acc * (space * 2) + space, spaced2);
			}
		}
	}
	ghost predicate last_position_is_sum_of_old_elements_rec_(original_elements: seq<int>, a: seq<int>, lower_bound: nat, space: nat)
		decreases space
		requires |original_elements| == |a|
		requires is_power_of_2(space)
		requires is_power_of_2(|a|)
		requires lower_bound + space * 2 <= |a|
	{
		a[lower_bound + space - 1] == sum(original_elements[lower_bound..lower_bound + space])
		&&
		(space > 1 ==> (
			var spaced2: nat :| spaced2 < space && is_power_of_2(spaced2) && space == spaced2 * 2;
			last_position_is_sum_of_old_elements_rec_(original_elements, a, lower_bound, spaced2)
			&&
			last_position_is_sum_of_old_elements_rec_(original_elements, a, lower_bound + space, spaced2)
		))
	}

	lemma section_end_within_bounds_(a: seq<int>, start: nat, space: nat)
		requires is_power_of_2(space)
		requires is_power_of_2(|a|)
		requires start < |a| / space
	//
		ensures start * space + space <= |a|
	{
		monotonicity_under_plain_multiplication(start, |a| / space - 1, space);
		multiplicative_inverse_property_between_powers_of_2(|a|, space);
	}

	ghost predicate last_position_is_sum_of_old_elements_(original_elements: seq<int>, a: seq<int>, start: nat, space: nat)
		requires |original_elements| == |a|
		requires is_power_of_2(space)
		requires is_power_of_2(|a|)
		requires start < |a| / space
	{
		section_end_within_bounds(a, start, space);
		a[start * space + space - 1] == sum(original_elements[start * space..start * space + space])
		&&
		(space > 1 ==> (
			var spaced2: nat :| spaced2 < space && is_power_of_2(spaced2) && space == spaced2 * 2;
			assert start * space + spaced2 * 2 <= |a|;
			last_position_is_sum_of_old_elements_rec_(original_elements, a, start * space, spaced2)
		))
	}

	lemma {:induction false} acc_at_end_after_loop(acc: nat, a: array<int>, left: nat, space: nat)
		requires left_within_bounds: left >= a.Length
		requires left_wrt_acc: left == acc * space * 2 + space - 1
		requires acc_lt_len_div_space_mul_2: acc <= a.Length / (space * 2)
		requires len_is_power_of_2: is_power_of_2(a.Length)
		requires space_is_power_of_2: is_power_of_2(space)
		requires space_lt_len: space <= a.Length / 2
	//
		ensures acc == a.Length / (space * 2)
	{
		assert acc == a.Length / (space * 2) by {
			assert space * 2 > 0 by {
				reveal space_is_power_of_2;
			}
			if acc < a.Length / (space * 2) {
				assert left < a.Length by {
					assert left <= a.Length - space - 1 by {
						assert acc * space * 2 <= a.Length - space * 2 by {
							assert acc * space * 2 <= a.Length / (space * 2) * (space * 2) - space * 2 by {
								assert acc * space * 2 <= (a.Length / (space * 2) - 1) * (space * 2) by {
									assert acc <= a.Length / (space * 2) - 1 by {
										reveal acc_lt_len_div_space_mul_2;
									}
									monotonicity_under_plain_multiplication(acc, a.Length / (space * 2) - 1, space * 2);
								}
							}
							multiplicative_inverse_property_between_powers_of_2(a.Length, space * 2) by {
								reveal len_is_power_of_2;
								reveal space_is_power_of_2;
								reveal space_lt_len;
							}
						}
						reveal left_wrt_acc;
					}
				}
				reveal left_within_bounds;
			} else {
				reveal acc_lt_len_div_space_mul_2;
			}
		}
	}
//

method upsweep_inner_inner_loop(ghost original_elements: seq<int>, a: array<int>, space: nat, left: nat, acc: nat)
	modifies a
	requires lengths_are_equal: |original_elements| == a.Length
	requires len_is_power_of_2: is_power_of_2(a.Length)
	requires space_is_power_of_2: is_power_of_2(space)
	requires space_mul_2_le_len: 1 <= space <= a.Length / 2

	requires left_wrt_acc: left == acc * space * 2 + space - 1
	requires left_bound: space - 1 <= left <= a.Length - space - 1
	requires fourth_acc_bound: 0 <= acc * space * 2 <= a.Length - space * 2
	requires third_acc_bound: 0 <= acc * 2 <= a.Length / space - 2
	requires second_acc_bound: 0 <= acc * space <= a.Length / 2 - space
	requires first_acc_bound: 0 <= acc <= a.Length / (space * 2) - 1
	requires computed_until_acc: sums_s_to_s_until_n_are_computed(original_elements, a[..], space * 2, 0, acc)
	requires computed_from_acc_mul_2: sums_s_to_s_until_n_are_computed(original_elements, a[..], space, acc * 2, a.Length / space)
//
	ensures sums_s_to_s_until_n_are_computed(original_elements, a[..], space * 2, 0, acc + 1)
	ensures sums_s_to_s_until_n_are_computed(original_elements, a[..], space, (acc + 1) * 2, a.Length / space)
{
	var right: nat := left + space;
	ghost var before: seq<int> := a[..];
	assert before_small_sums: sums_s_to_s_until_n_are_computed(original_elements, before, space, acc * 2, a.Length / space) by {
		reveal lengths_are_equal;
		reveal len_is_power_of_2;
		reveal space_is_power_of_2;
		reveal computed_from_acc_mul_2;
	}
	a[right] := a[left] + a[right] by {
		reveal left_wrt_acc;
		reveal fourth_acc_bound;
	}
	calculated_sums_for_currect_iteration(original_elements, before, a, space * 2, acc) by {
		reveal lengths_are_equal;
		reveal space_is_power_of_2;
		reveal len_is_power_of_2;
		reveal space_mul_2_le_len;
		reveal first_acc_bound;
		reveal computed_until_acc;
		assert before[..acc * (space * 2)] == a[..acc * (space * 2)] by {
			assert before[..left - space + 1] == a[..left - space + 1] by {
				reveal left_wrt_acc;
				reveal fourth_acc_bound;
			}
			calc == {
				left - space + 1;
				{ reveal left_wrt_acc; }
				acc * space * 2 + space - 1 - space + 1;
				acc * space * 2;
				acc * (space * 2);
			}
		}
		array_change_resulted_in_next_sum(original_elements, before, a, space, acc) by {
			reveal lengths_are_equal;
			reveal space_is_power_of_2;
			reveal len_is_power_of_2;
			reveal space_mul_2_le_len;
			reveal first_acc_bound;
			reveal third_acc_bound;
			reveal fourth_acc_bound;

			assert a[acc * space * 2 + space * 2 - 1] == before[acc * space * 2 + space - 1] + before[acc * space * 2 + space * 2 - 1] by {
				assert a[right] == before[left] + before[right];
				reveal left_wrt_acc;
			}

			reveal before_small_sums;
		}
	}
	rest_of_previous_sums_are_kept(original_elements, before, a, space, acc) by {
		reveal lengths_are_equal;
		reveal space_is_power_of_2;
		reveal len_is_power_of_2;
		reveal space_mul_2_le_len;
		reveal first_acc_bound;
		reveal third_acc_bound;
		reveal fourth_acc_bound;
		reveal computed_from_acc_mul_2;
		assert before[(acc + 1) * 2 * space..] == a[(acc + 1) * 2 * space..] by {
			assert before[right + 1..] == a[right + 1..];
			calc == {
				right + 1;
				left + space + 1;
				{ reveal left_wrt_acc; }
				acc * space * 2 + space - 1 + space + 1;
				acc * space * 2 + space * 2;
				(acc + 1) * space * 2;
				{ assert forall a: nat, b: nat, c: nat :: a * b * c == a * c * b; }
				(acc + 1) * 2 * space;
			}
		}
	}
}

method upsweep_inner_loop(ghost original_elements: seq<int>, a: array<int>, space: nat)
	modifies a
	requires |original_elements| == a.Length
	requires is_power_of_2(a.Length)
	requires is_power_of_2(space)
	requires 1 <= space <= a.Length / 2
	requires sums_s_to_s_until_n_are_computed(original_elements, a[..], space, 0, a.Length / space)
//
	ensures sums_s_to_s_until_n_are_computed(original_elements, a[..], space * 2, 0, a.Length / (space * 2))
{
	var left: nat := space - 1;
	var acc: nat := 0;
	sums_s_to_s_are_computed(original_elements, a, space, acc);
	while left < a.Length
		invariant space - 1 <= left <= a.Length + space - 1
		invariant left == acc * space * 2 + space - 1
		invariant 0 <= acc * space * 2 <= a.Length
		invariant 0 <= acc * 2 <= a.Length / space
		invariant 0 <= acc * space <= a.Length / 2
		invariant 0 <= acc <= a.Length / (space * 2)
		invariant sums_s_to_s_until_n_are_computed(original_elements, a[..], space * 2, 0, acc)
		invariant sums_s_to_s_until_n_are_computed(original_elements, a[..], space, acc * 2, a.Length / space)
	{
		acc_bounds_within_loop(left, acc, a, space);
		left_bounds_within_loop(left, acc, a, space);
		upsweep_inner_inner_loop(original_elements, a, space, left, acc);
		calc == {
			left + space * 2;
			acc * space * 2 + space - 1 + space * 2;
			(acc + 1) * space * 2 + space - 1;
		}
		left := left + space * 2;
		acc := acc + 1;
	}
	acc_at_end_after_loop(acc, a, left, space);
}

method upsweep_iter(a: array<int>)
	modifies a
	requires is_power_of_2(a.Length)
//
	ensures a[a.Length - 1] == sum(old(a[..]))
{
	ghost var original_elements: seq<int> := a[..];
	var space: nat := 1;
	var log_space: nat := 0;
	assert sums_s_to_s_until_n_are_computed(original_elements, a[..], space, 0, a.Length / space) by {
		sums_of_1_are_computed_at_the_beginning(original_elements, a);
	}
	while space < a.Length
		invariant is_power_of_2(space)
		invariant is_2_to_the_power_of(space, log_space)
		invariant 1 <= space <= a.Length
		invariant 0 <= log_space <= log_of_power_of_2(a.Length)
		invariant space == two_to_the_power_of(log_space)
		invariant sums_s_to_s_until_n_are_computed(original_elements, a[..], space, 0, a.Length / space)
	{
		assert log_space < log_of_power_of_2(a.Length) by {
			if log_space == log_of_power_of_2(a.Length) {
				assert space == a.Length by {
					assert space == two_to_the_power_of(log_space);
					assert a.Length == two_to_the_power_of(log_of_power_of_2(a.Length)) by {
						exponent_logarithm_identity(a.Length);
					}
					monotonicity_under_logarithmization_between_powers_of_2(space, a.Length);
				}
			}
		}
		assert space <= a.Length / 2 by {
			monotonicity_under_logarithmization_between_powers_of_2(space, a.Length);
		}
		upsweep_inner_loop(original_elements, a, space);
		space := space * 2;
		log_space := log_space + 1;
	}
	assert a[a.Length - 1] == sum(original_elements) by {
		assert space == a.Length;
		assert a[space - 1] == sum(original_elements[0..0 + space]) by {
			assert last_position_is_sum_of_old_elements(original_elements, a[..], 0, space);// by {
				// assert forall start: nat {:trigger} :: 0 <= start < a.Length / space ==> last_position_is_sum_of_old_elements(original_elements, a[..], start, space) by {
					// assert sums_s_to_s_until_n_are_computed(original_elements, a[..], space, 0, a.Length / space);
				// }
				// assert a.Length / space == 1;
			// }
		}
		assert original_elements == original_elements[0..0 + space];
	}
}
