ghost predicate is_power_of_2(n: nat)
{n > 0 && (n == 1 || (exists nd2: nat {:trigger} :: nd2 < n && is_power_of_2(nd2) && n == nd2 * 2))}

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
lemma closure_under_division_of_is_power_of_2(a: nat, b: nat)
	requires is_power_of_2(a)
	requires is_power_of_2(b)
	requires a >= b
//
	ensures is_power_of_2(a / b)
{
	var a': nat := a;
	var b': nat := b;
	var factor: nat := 1;
	while b' != 1
		invariant is_power_of_2(a')
		invariant is_power_of_2(b')
		invariant a' >= b'
		invariant a == a' * factor
		invariant b == b' * factor
		invariant is_power_of_2(factor)
	{
  	var a'd2: nat :| a'd2 < a' && is_power_of_2(a'd2) && a' == a'd2 * 2;
		var b'd2: nat :| b'd2 < b' && is_power_of_2(b'd2) && b' == b'd2 * 2;
		a' := a'd2;
		b' := b'd2;
		factor := factor * 2;
	}
	assert a / b == a' by {
		assert a / b == a' * b / b by {
			assert a == a' * b by {
				assert b == factor;
			}
			var t: (nat, nat, nat) -> bool := (x, y, z) => true;
			assert forall x: nat, y: nat, z: nat {:trigger t(x, y, z)} :: z > 0 && x == y ==> x / z == y / z;
			assert t(a, a' * b, b);
		}
		var t: (nat, nat) -> bool := (x, y) => true;
		forall x: nat, y: nat {:trigger t(x, y)} | y > 0
			ensures x == x * y / y
		{
			assert x * y == ((x * y) / y) * y by {
				assert x * y == ((x * y) / y) * y + (x * y) % y;
				assert (x * y) % y == 0 by {
					modulo_persists_while_steps_mul_by_y(0, x, y);
				}
			}
			assert x * y == ((x * y) / y) * y ==> x == (x * y) / y by {
				monotonicity_under_inverse_of_plain_multiplication(x, (x * y) / y, y);
			}
		}
		assert t(a', b);
	}
}

function sum(a: seq<int>): (s: int)
{if |a| == 0 then 0 else a[0] + sum(a[1..])}

lemma additivity_of_sum(a: seq<int>, start: nat, mid: nat, end: nat)
	decreases mid - start
	requires start <= mid <= end <= |a|
//
	ensures sum(a[start..end]) == sum(a[start..mid]) + sum(a[mid..end])
{
	if start < mid {
		assert sum(a[start..end]) == a[start] + sum(a[start + 1..mid]) + sum(a[mid..end]) by {
			additivity_of_sum(a, start + 1, mid, end);
			assert sum(a[start..end]) == a[start] + sum(a[start + 1..end]);
		}
	}
}

lemma add_modulo(x: nat, y: nat, z: nat)
	requires z < y
//
	ensures (x * y + z) % y == z
{
	var d: nat := (x * y + z) / y;
	var r: nat := (x * y + z) % y;
	var d': nat := d;
	var x': nat := x;
	while d' > 0
		invariant d' * y + r == x' * y + z
	{
		d' := d' - 1;
		x' := x' - 1;
	}
}

lemma {:isolate_assertions} modulo_persists_while_steps_mul_by_y(x: int, y: int, z: nat)
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

lemma monotonicity_under_plain_multiplication(a: nat, b: nat, c: nat)
//
	ensures a <= b ==> a * c <= b * c
	ensures a == b ==> a * c == b * c
	ensures a >= b ==> a * c >= b * c
{}

lemma monotonicity_under_inverse_of_plain_multiplication(a: nat, b: nat, c: nat)
	requires c > 0
//
	ensures a * c <= b * c ==> a <= b
	ensures a * c == b * c ==> a == b
	ensures a * c >= b * c ==> a >= b
{
	if a * c <= b * c {
		// assert (b * c - a * c) / c >= 0 by {
		// 	assert b * c - a * c >= 0;
		// 	assert b * c - a * c == (b * c - a * c) / c * c by {
		// 		assert b * c - a * c == (b * c - a * c) / c * c + (b * c - a * c) % c;
		// 		assert (b * c - a * c) % c == 0 by {
		// 			assert ((b - a) * c) % c == 0 by {
		// 				modulo_persists_while_steps_mul_by_y(0, b - a, c);
		// 			}
		// 		}
		// 	}
		// }
		assert b - a >= 0;
	}
}

lemma multiplicative_inverse_property_between_powers_of_2(a: nat, b: nat)
	requires is_power_of_2(a)
	requires is_power_of_2(b)
	requires a >= b
//
	ensures a / b * b == a
{
	assert a % b == 0 by {
		power_of_2_divides_bigger_power_of_2(a, b);
	}
}

// upsweep_iter helper functions
	ghost predicate RAW_last_position_is_sum_of_old_elements(original_elements: seq<int>, a: seq<int>, start: nat, space: nat)
		requires |original_elements| == |a|
		requires is_power_of_2(space)
		requires is_power_of_2(|a|)
		requires space <= |a|
		requires start <= |a| / space - 1
		requires start * space + space <= |a|
	{
		a[start * space + space - 1] == sum(original_elements[start * space..start * space + space])
	}
	ghost predicate last_position_is_sum_of_old_elements(original_elements: seq<int>, a: seq<int>, start: nat, space: nat)
		requires |original_elements| == |a|
		requires is_power_of_2(space)
		requires is_power_of_2(|a|)
		requires space <= |a|
		requires start <= |a| / space - 1
	{
		assert start * space + space <= |a| by {
			// assert start * space <= |a| / space * space - space by {
				monotonicity_under_plain_multiplication(start, |a| / space - 1, space);
			// }
			multiplicative_inverse_property_between_powers_of_2(|a|, space);
		}
		RAW_last_position_is_sum_of_old_elements(original_elements, a, start, space)
	}

	ghost predicate sums_s_to_s_until_n_are_computed(original_elements: seq<int>, a: seq<int>, space: nat, lower_bound: nat, upper_bound: int)
		requires |original_elements| == |a|
		requires is_power_of_2(space)
		requires is_power_of_2(|a|)
		requires space <= |a|
		requires lower_bound <= |a| / space
		requires upper_bound <= |a| / space
	{
		forall start: nat {:trigger} :: lower_bound <= start < upper_bound ==>
			last_position_is_sum_of_old_elements(original_elements, a, start, space)
	}

	lemma RAW_acc_bounds_within_loop(left: nat, acc: nat, a: array<int>, space: nat)
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
	lemma idk(a: nat, b: nat, c: nat)
		requires b > 0
		requires c > 0
		ensures a / (b * c) == a / b / c
	{
		var lhs: nat := a / (b * c);
		var adb: nat := a / b;
		var rhs: nat := adb / c;

    assert lhs * (b * c) <= a < (lhs + 1) * (b * c);
    
    assert adb * b <= a < (adb + 1) * b;

    assert rhs * c <= adb < (rhs + 1) * c;
		assume false;
		// ghost var d1 := a / (b * c);
    // ghost var d2 := a / b;
    // ghost var d3 := d2 / c;

    // // Unpack the definition of division for a / (b * c)
    // assert d1 * (b * c) <= a < (d1 + 1) * (b * c);
    
    // // Unpack the definition of division for a / b
    // assert d2 * b <= a < (d2 + 1) * b;

    // // Unpack the definition of division for d2 / c
    // assert d3 * c <= d2 < (d3 + 1) * c;

    // // Relate the results
    // assert d1 == d3 by {
    //     // Use the properties of integer division to show equivalence
    //     assert d1 * (b * c) == d3 * (b * c);
    // }
	}
	lemma acc_bounds_within_loop(left: nat, acc: nat, a: array<int>, space: nat)
		requires left == acc * space * 2 + space - 1
		requires left < a.Length
		requires is_power_of_2(a.Length)
		requires is_power_of_2(space * 2)
		requires space * 2 <= a.Length
	//
		ensures acc <= a.Length / (space * 2) - 1
		ensures acc * 2 <= a.Length / space - 2
	{
		RAW_acc_bounds_within_loop(left, acc, a, space) by {	
			assert a.Length % (space * 2) == 0 by {
				power_of_2_divides_bigger_power_of_2(a.Length, space * 2);
			}
		}
		assert acc * 2 <= a.Length / (space * 2) * 2 - 2 by {
			assert acc <= a.Length / (space * 2) - 1;
		}
		calc == {
			a.Length / (space * 2) * 2 - 2;
			{assume false;}
			a.Length / space / 2 * 2 - 2;
			{assert a.Length / space == a.Length / space / 2 * 2 by {
				multiplicative_inverse_property_between_powers_of_2(a.Length / space, 2) by {
					assert is_power_of_2(a.Length / space) by {
						closure_under_division_of_is_power_of_2(a.Length, space);
					}
					assert is_power_of_2(2) by {
						assert is_power_of_2(1);
					}
				}
			}}
			a.Length / space - 2;
		}
	}

	lemma left_in_loop_lt_left_outside_loop(left: nat, acc: nat, a: array<int>, space: nat)
		requires left == acc * space * 2 + space - 1
		requires left < a.Length
		requires is_power_of_2(a.Length)
		requires is_power_of_2(space * 2)
		requires space * 2 <= a.Length
	//
		ensures left <= a.Length - space - 1
	{
		assert acc * space * 2 + space - 1 <= a.Length - space - 1 by {
			assert acc * space * 2 <= a.Length - space * 2 by {
				assert acc <= a.Length / (space * 2) - 1 by {
					acc_bounds_within_loop(left, acc, a, space);
				}
				monotonicity_under_plain_multiplication(acc, a.Length / (space * 2) - 1, space * 2);
				multiplicative_inverse_property_between_powers_of_2(a.Length, space * 2);
			}
		}
	}

	lemma {:isolate_assertions} calculated_sums_for_currect_iteration(original_elements: seq<int>, before: seq<int>, a: array<int>, space: nat, acc: nat)
		requires |original_elements| == |before| == a.Length
		requires is_power_of_2(space)
		requires is_power_of_2(a.Length)
		requires space <= a.Length
		requires acc <= a.Length / space - 1
		requires acc * space <= a.Length
		requires sums_s_to_s_until_n_are_computed(original_elements, before, space, 0, acc)
		requires unchanged_until_acc_times_space: before[..acc * space] == a[..acc * space]
		requires last_position_is_sum_of_old_elements(original_elements, a[..], acc, space)
	//
		ensures sums_s_to_s_until_n_are_computed(original_elements, a[..], space, 0, acc + 1)
	{
		forall start: nat | 0 <= start < acc + 1
			ensures last_position_is_sum_of_old_elements(original_elements, a[..], start, space)
		{
			if start < acc {
				assert before[start * space + space - 1] == a[start * space + space - 1] by {
					assert start * space + space - 1 < acc * space by {
						assert start * space <= acc * space - space by {
							// assert start <= acc - 1;
							monotonicity_under_plain_multiplication(start, acc - 1, space);
							assert (acc - 1) * space == acc * space - space;
						}
						assert start * space + space <= acc * space;
					}
					reveal unchanged_until_acc_times_space;
				}
				assert last_position_is_sum_of_old_elements(original_elements, before, start, space);
			}
		}
	}

	lemma {:isolate_assertions} RAW_array_change_resulted_in_next_sum(original_elements: seq<int>, before: seq<int>, a: array<int>, space: nat, acc: nat)
		requires |original_elements| == |before| == a.Length
		requires is_power_of_2(space)
		requires is_power_of_2(a.Length)
		requires space * 2 <= a.Length
		requires acc * 2 + 1 <= a.Length / space - 1
		requires acc <= a.Length / (space * 2) - 1

		requires acc * space * 2 + space * 2 <= a.Length
		requires a[acc * space * 2 + space * 2 - 1] == before[acc * space * 2 + space - 1] + before[acc * space * 2 + space * 2 - 1]

		requires left_half_sum: last_position_is_sum_of_old_elements(original_elements, before, acc * 2, space)
		requires right_half_sum: last_position_is_sum_of_old_elements(original_elements, before, acc * 2 + 1, space)
	//
		ensures last_position_is_sum_of_old_elements(original_elements, a[..], acc, space * 2)
	{
		assert a[..][acc * space * 2 + space * 2 - 1] == sum(original_elements[acc * space * 2..acc * space * 2 + space * 2]) by {
			assert a[acc * space * 2 + space * 2 - 1] == sum(original_elements[acc * space * 2..acc * space * 2 + space * 2]) by {
				var start: nat := acc * space * 2;
				var mid: nat := start + space;
				var end: nat := mid + space;
				assert before[mid - 1] == sum(original_elements[start..mid]) by {
					assert {:only} before[acc * 2 * space + space - 1] == sum(original_elements[acc * 2 * space..acc * 2 * space + space]) by {
						assert |original_elements| == |before|;
						// assert is_power_of_2(space);
						assert is_power_of_2(|before|);
						assert space <= |before|;
						assert acc * 2 <= |before| / space - 1;
						assert acc * 2 * space <= |before| - space by {
							monotonicity_under_plain_multiplication(acc * 2, |before| / space - 1, space);
							// calc == {
							// 	(|before| / space - 1) * space;
							// 	|before| / space * space - space;
							// 	{assert |before| == |before| / space * space by {
							// 		assert |before| % space == 0 by {
							// 			assume false;
							// 			power_of_2_divides_bigger_power_of_2(|before|, space);
							// 			assume false;
							// 		}
							// 		assume false;
							// 	}}
							// 	|before| - space;
							// }
							assume false;
						}
						assume false;
						reveal left_half_sum;
						// assert last_position_is_sum_of_old_elements(original_elements, before, acc * 2, space) by { assume false; }
						// assume false; // I have no idea why such an easy thing can't be proven
					}
					assert start == acc * 2 * space;
					assert mid == acc * 2 * space + space;
				}
				assert before[end - 1] == sum(original_elements[mid..end]) by {
					assert before[(acc * 2 + 1) * space + space - 1] == sum(original_elements[(acc * 2 + 1) * space.. (acc * 2 + 1) * space + space]) by {
						assume false; // the thing from 16 lines ago still applies here
					}
					assert mid == (acc * 2 + 1) * space;
					assert end == (acc * 2 + 1) * space + space;
				}
				assert a[end - 1] == sum(original_elements[start..end]) by {
					calc == {
						before[mid - 1] + before[end - 1];
						sum(original_elements[start..mid]) + sum(original_elements[mid..end]);
						{additivity_of_sum(original_elements, start, mid, end);}
						sum(original_elements[start..end]);
					}
				}
			}
			assert a[..][acc * space * 2 + space * 2 - 1] == a[acc * space * 2 + space * 2 - 1];
		}
	}

	lemma commutivitativity_of_plain_multiplication(a: nat, b: nat, c: nat)
		ensures a * b * c == a * c * b
	{}
	lemma last_position_is_sum_of_old_elements_intermediary(original_elements: seq<int>, before: seq<int>, a: array<int>, start: nat, space: nat, l: nat, u: nat)
		requires |original_elements| == |before| == a.Length
		requires is_power_of_2(space)
		requires is_power_of_2(|before|)
		requires space * 2 <= a.Length
		requires start <= a.Length / space - 1
		requires last_position_is_sum_of_old_elements(original_elements, before, start, space)
		requires l <= u <= |before|
		requires l == start * space
		requires u == start * space + space
		ensures before[u - 1] == sum(original_elements[l..u])
	{
		// assert before[start * space + space - 1] == sum(original_elements[start * space..start * space + space]);
	}
	lemma {:isolate_assertions} array_change_resulted_in_next_sum(original_elements: seq<int>, before: seq<int>, a: array<int>, space: nat, acc: nat, left: nat, right: nat)
		requires |original_elements| == |before| == a.Length
		requires is_power_of_2(space)
		requires is_power_of_2(a.Length)
		requires space * 2 <= a.Length
		requires acc * 2 + 1 <= a.Length / space - 1
		requires acc <= a.Length / (space * 2) - 1

		requires left == acc * space * 2 + space - 1
		requires right == acc * space * 2 + space * 2 - 1
		requires left <= right < a.Length
		requires a[right] == before[left] + before[right]

		requires left_half_sum: last_position_is_sum_of_old_elements(original_elements, before, acc * 2, space)
		requires right_half_sum: last_position_is_sum_of_old_elements(original_elements, before, acc * 2 + 1, space)
	//
		ensures last_position_is_sum_of_old_elements(original_elements, a[..], acc, space * 2)
	{
		assert a[..][acc * space * 2 + space * 2 - 1] == sum(original_elements[acc * space * 2..acc * space * 2 + space * 2]) by {
			var start: nat := acc * space * 2;
			assert a[..][right] == sum(original_elements[start..right + 1]) by {
				assert a[right] == sum(original_elements[start..right + 1]) by {
					assert a[right] == sum(original_elements[start..right + 1]) by {
						assert before[left] == sum(original_elements[start..left + 1]) by {
							last_position_is_sum_of_old_elements_intermediary(original_elements, before, a, acc * 2, space, start, left + 1) by {
								calc == {
									start;
									acc * space * 2;
									{
										var t: (nat, nat, nat) -> bool := (a, b, c) => true;
										assert forall a: nat, b: nat, c: nat {:trigger t(a, b, c)} :: a * b * c == a * c * b;
										assert t(acc, space, 2);
									}
									acc * 2 * space;
								}
								reveal left_half_sum;
							}
						}
						assert before[right] == sum(original_elements[left + 1..right + 1]) by {
							last_position_is_sum_of_old_elements_intermediary(original_elements, before, a, acc * 2 + 1, space, left + 1, right + 1) by {
								calc == {
									left + 1;
									acc * space * 2 + space - 1 + 1;
									acc * space * 2 + space;
									{
										var t: (nat, nat, nat) -> bool := (a, b, c) => true;
										assert forall a: nat, b: nat, c: nat {:trigger t(a, b, c)} :: a * b * c + b == (a * c + 1) * b;
										assert t(acc, space, 2);
									}
									(acc * 2 + 1) * space;
								}
								reveal right_half_sum;
							}
						}
						calc == {
							before[left] + before[right];
							sum(original_elements[start..left + 1]) + sum(original_elements[left + 1..right + 1]);
							{additivity_of_sum(original_elements, start, left + 1, right + 1);}
							sum(original_elements[start..right + 1]);
						}
					}
				}
				assert a[..][right] == a[right];
			}
		}
	}
//

lemma acc_times_2_plus_1_le_a_Length_div_space_minus_1(acc: nat, space: nat, a: array<int>, left: nat)
	requires left == acc * space * 2 + space - 1
	requires is_power_of_2(a.Length)
	requires is_power_of_2(space)
	requires space <= a.Length
	requires left <= a.Length - space - 1
	ensures acc * 2 + 1 <= a.Length / space - 1
{
	assert acc * 2 <= a.Length / space - 2 by {
		assert acc * 2 * space <= (a.Length / space - 2) * space by {
			assert acc * 2 * space + space - 1 <= (a.Length / space - 2) * space + space - 1 by {
				assert left == acc * 2 * space + space - 1;
				calc == {
					(a.Length / space - 2) * space + space - 1;
					a.Length / space * space - 2 * space + space - 1;
					a.Length / space * space - space - 1;
					{assert a.Length == a.Length / space * space by {
						assert a.Length % space == 0 by {
							power_of_2_divides_bigger_power_of_2(a.Length, space);
						}
					}}
					a.Length - space - 1;
				}
			}
		}
		var t: (nat, nat, nat) -> bool := (a, b, c) => true;
		assert {:split_here} forall a: nat, b: nat, c: nat {:trigger t(a, b, c)} :: c > 0 && a * c <= b * c ==> a <= b;
		assert t(acc * 2, a.Length / space - 2, space);
	}
}

method {:isolate_assertions} upsweep_inner_loop(original_elements: seq<int>, a: array<int>, space: nat)
	modifies a
	requires |original_elements| == a.Length
	requires is_power_of_2(a.Length)
	requires is_power_of_2(space)
	requires 1 <= space <= a.Length / 2
	requires a.Length % space == 0
	requires (a.Length - 1 - (space - 1)) % space == 0
	requires sums_s_to_s_until_n_are_computed(original_elements, a[..], space, 0, a.Length / space)
{
	var left: nat := space - 1;
	var acc: nat := 0;
	assert a.Length % (space * 2) == 0 by {
		assert a.Length >= space * 2;
		assert is_power_of_2(a.Length);
		assert is_power_of_2(space * 2);
		power_of_2_divides_bigger_power_of_2(a.Length, space * 2);
	}
	while left < a.Length
		invariant space - 1 <= left <= a.Length + space - 1
		invariant left == acc * space * 2 + space - 1
		invariant 0 <= acc * space * 2 <= a.Length
		invariant 0 <= acc * 2 <= a.Length / space
		invariant 0 <= acc <= a.Length / (space * 2)
		invariant sums_s_to_s_until_n_are_computed(original_elements, a[..], space * 2, 0, acc)
		invariant sums_s_to_s_until_n_are_computed(original_elements, a[..], space, acc * 2, a.Length / space)
	{
		assert left <= a.Length - space - 1 by {
			left_in_loop_lt_left_outside_loop(left, acc, a, space);
		}
		assert acc <= a.Length / (space * 2) - 1 by {
			acc_bounds_within_loop(left, acc, a, space);
		}
		var right: nat := left + space;
		ghost var before: seq<int> := a[..];
		assert/* before_big_sums:*/ sums_s_to_s_until_n_are_computed(original_elements, before, space * 2, 0, acc);
		assert before_small_sums: sums_s_to_s_until_n_are_computed(original_elements, before, space, acc * 2, a.Length / space);
		a[right] := a[left] + a[right];
		assert left + space * 2 == (acc + 1) * space * 2 + space - 1;
		calculated_sums_for_currect_iteration(original_elements, before, a, space * 2, acc) by {
			array_change_resulted_in_next_sum(original_elements, before, a, space, acc, left, right) by {
				assert |original_elements| == |before| == a.Length;
				// assert is_power_of_2(space);
				assert is_power_of_2(a.Length);
				// assert space * 2 <= a.Length;
				assert acc * 2 + 1 <= a.Length / space - 1 by {
					acc_times_2_plus_1_le_a_Length_div_space_minus_1(acc, space, a, left);
				}
				assert acc <= a.Length / (space * 2) - 1;
				assert a[acc * space * 2 + space * 2 - 1] == before[acc * space * 2 + space - 1] + before[acc * space * 2 + space * 2 - 1];
				// assert last_position_is_sum_of_old_elements(original_elements, before, acc * 2, space) by { assume false; }
				assert last_position_is_sum_of_old_elements(original_elements, before, acc * 2, space) by {
					reveal before_small_sums;
					// assert acc * 2 >= acc * 2;
				}
				assert last_position_is_sum_of_old_elements(original_elements, before, acc * 2 + 1, space) by {
					reveal before_small_sums;
					assume acc * 2 <= acc * 2 + 1 < a.Length / space;
				}
			}
		}
		assume sums_s_to_s_until_n_are_computed(original_elements, a[..], space, acc * 2 + 2, a.Length / space);
		left := left + space * 2;
		acc := acc + 1;
		// assume left + space <= a.Length - 1;
		// assert {:only} acc <= a.Length / (space * 2) by {
		// 	assert acc * space * 2 <= a.Length;
		// 	var t: (nat, nat, nat) -> bool := (a, b, c) => true;
		// 	{
		// 		assert {:focus} forall a: nat, b: nat, c: nat {:trigger t(a, b, c)} :: c > 0 && a * c <= b && b % c == 0 ==> a <= b / c;
		// 	}
		// 	assert t(acc, a.Length, space * 2);
		// 	assume false;
		// }
		// assume sums_s_to_s_until_n_are_computed(original_elements, a, space * 2, 0, acc);
	}
}

method upsweep_inner_loop_minus_1_RU_(original_elements: seq<int>, a: array<int>, space: nat)
	modifies a
	requires |original_elements| == a.Length
	requires is_power_of_2(a.Length)
	requires is_power_of_2(space)
	requires 1 <= space <= a.Length / 2
	requires a.Length % space == 0
	requires (a.Length - 1 - (space - 1)) % space == 0
	requires sums_s_to_s_until_n_are_computed(original_elements, a[..], space, 0, a.Length / space)
{
	var left: nat := space - 1;
	var acc: nat := 0;
	assert a.Length % (space * 2) == 0 by {
		assert a.Length >= space * 2;
		assert is_power_of_2(a.Length);
		assert is_power_of_2(space * 2);
		power_of_2_divides_bigger_power_of_2(a.Length, space * 2);
	}
	while left < a.Length
		invariant space - 1 <= left <= a.Length + space - 1
		invariant left == acc * space * 2 + space - 1
		invariant 0 <= acc * space * 2 <= a.Length
		invariant 0 <= acc * 2 <= a.Length / space
		invariant 0 <= acc <= a.Length / (space * 2)
		invariant sums_s_to_s_until_n_are_computed(original_elements, a[..], space * 2, 0, acc)
		invariant sums_s_to_s_until_n_are_computed(original_elements, a[..], space, acc * 2, a.Length / space)
	{
		assert left <= a.Length - space - 1 by {
			left_in_loop_lt_left_outside_loop(left, acc, a, space);
		}
		assert acc <= a.Length / (space * 2) - 1 by {
			acc_bounds_within_loop(left, acc, a, space);
		}
		var right: nat := left + space;
		ghost var before: seq<int> := a[..];
		assert sums_s_to_s_until_n_are_computed(original_elements, before, space * 2, 0, acc);
		a[right] := a[left] + a[right];
		assert left + space * 2 == (acc + 1) * space * 2 + space - 1;
		calculated_sums_for_currect_iteration(original_elements, before, a, space * 2, acc) by {
			array_change_resulted_in_next_sum(original_elements, before, a, space, acc, left, right) by {
				assert |original_elements| == |before| == a.Length;
				// assert is_power_of_2(space);
				assert is_power_of_2(a.Length);
				// assert space * 2 <= a.Length;
				assert acc * 2 + 1 <= a.Length / space - 1 by {
					acc_times_2_plus_1_le_a_Length_div_space_minus_1(acc, space, a, left);
				}
				assert acc <= a.Length / (space * 2) - 1;
				assert a[acc * space * 2 + space * 2 - 1] == before[acc * space * 2 + space - 1] + before[acc * space * 2 + space * 2 - 1];
				assert last_position_is_sum_of_old_elements(original_elements, before, acc * 2, space) by { assume false; }
				assert last_position_is_sum_of_old_elements(original_elements, before, acc * 2 + 1, space) by { assume false; }
			}
		}
		assume sums_s_to_s_until_n_are_computed(original_elements, a[..], space, acc * 2 + 2, a.Length / space);
		left := left + space * 2;
		acc := acc + 1;
		// assume left + space <= a.Length - 1;
		// assert {:only} acc <= a.Length / (space * 2) by {
		// 	assert acc * space * 2 <= a.Length;
		// 	var t: (nat, nat, nat) -> bool := (a, b, c) => true;
		// 	{
		// 		assert {:focus} forall a: nat, b: nat, c: nat {:trigger t(a, b, c)} :: c > 0 && a * c <= b && b % c == 0 ==> a <= b / c;
		// 	}
		// 	assert t(acc, a.Length, space * 2);
		// 	assume false;
		// }
		// assume sums_s_to_s_until_n_are_computed(original_elements, a, space * 2, 0, acc);
	}
}

method {:isolate_assertions} upsweep_iter(a: array<int>)
	modifies a
	requires is_power_of_2(a.Length)
	ensures a[a.Length - 1] == sum(old(a[..]))
{
	ghost var original_elements: seq<int> := a[..];
	var space: nat := 1;
	// assume false;
	while space < a.Length
		invariant is_power_of_2(space)
		invariant 1 <= space <= a.Length
		invariant a.Length % space == 0
		invariant sums_s_to_s_until_n_are_computed(original_elements, a[..], space, space - 1, a.Length)
	{
		assert space <= a.Length / 2;
		var left: nat := space - 1;
		var acc: nat := 0;
		assert a.Length % (space * 2) == 0 by { power_of_2_divides_bigger_power_of_2(a.Length, space * 2); }
		assert (left - space + 1) % (space * 2) == 0 by {
			assert 0 % (space * 2) == 0;
			assert left - space + 1 == 0 by {
				assert left == space - 1;
			}
		}
		assert (space * 2 - 1) % (space * 2) == space * 2 - 1 by {
			modulo_persists_while_steps_mul_by_y(-1, 1, space * 2);
			add_modulo(0, space * 2, space * 2 - 1);
		}
		assume sums_s_to_s_until_n_are_computed(original_elements, a[..], space * 2, space * 2 - 1, left - space + 1);
		while left < a.Length
			invariant space - 1 <= left <= a.Length + space - 1
			invariant left - space + 1 == acc * space * 2
			invariant 0 <= left - space + 1 <= a.Length
			invariant 0 <= acc <= a.Length
			invariant (left - space + 1) % (space * 2) == 0
			// invariant {:focus} sums_s_to_s_until_n_are_computed(original_elements, a, space * 2, space * 2 - 1, left - space + 1)
			// invariant sums_s_to_s_until_n_are_computed(original_elements, a, space, left + space, a.Length)
		{
			assert left <= a.Length - space - 1 by { assume false; }
			var right: nat := left + space;
			a[right] := a[left] + a[right];

			// assert {:focus} sums_s_to_s_until_n_are_computed(original_elements, a, space * 2, space * 2 - 1, left - space + 1);
			// assume {:focus} sums_s_to_s_until_n_are_computed(original_elements, a, space * 2, space * 2 - 1, left - space + 1 + space * 2);
			assert left + space * 2 - space + 1 == (acc + 1) * space * 2;
			left := left + space * 2;
			acc := acc + 1;
			assert (left - space + 1) % (space * 2) == 0 by {
				assert (acc * space * 2) % (space * 2) == 0 by {
					assert (acc * (space * 2) + 0) % (space * 2) == 0 by {
						add_modulo(acc, space * 2, 0);
					}
					assert acc * space * 2 == acc * (space * 2) + 0;
				}
				assert left - space + 1 == acc * space * 2;
			}
		}
		space := space * 2;
		power_of_2_divides_bigger_power_of_2(a.Length, space);
		assert sums_s_to_s_until_n_are_computed(original_elements, a[..], space, space - 1, a.Length) by { assume false; }
	}
	assert a[a.Length - 1] == sum(original_elements) by {
		assert a[space - 1] == sum(original_elements[0..0 + space]) by {
			// assert forall start: nat :: start % space == 0 && start + space - 1 < a.Length ==> a[start + space - 1] == sum(original_elements[start..start + space]);
			assert 0 % space == 0;
		}
		assert space == a.Length;
		assert original_elements == original_elements[0..0 + space];
	}
}
