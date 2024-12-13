datatype Arb = Leaf | Node(left: Arb, middle: int, right: Arb)
{
//
}

class Tree {
	var info: int
	var left: Tree?
	var right: Tree?

	ghost var alg_tree: Arb

	ghost var repr: set<Tree>
	ghost var values: seq<int>
	// ghost var height: nat

	ghost predicate is_valid()
		reads this
		reads repr
		decreases repr
	{
		alg_tree.Node? &&
		(left == null && right == null ==> (
			repr == {this} &&
			values == [info] &&
			// height == 1 &&
			alg_tree == Node(Leaf, info, Leaf)
		)) &&
		(left != null && right == null ==> (
			left in repr &&
			left.repr < repr &&
			this !in left.repr &&
			repr == left.repr + {this} &&
			values == left.values + [info] &&
			left.is_valid() &&
			// height == left.height + 1 &&
			alg_tree == Node(left.alg_tree, info, Leaf)
		)) &&
		(left == null && right != null ==> (
			right in repr &&
			right.repr < repr &&
			this !in right.repr &&
			repr == {this} + right.repr &&
			values == [info] + right.values &&
			right.is_valid() &&
			// height == right.height + 1 &&
			alg_tree == Node(Leaf, info, right.alg_tree)
		)) &&
		(left != null && right != null ==> (
			left in repr &&
			right in repr &&
			left.repr < repr &&
			right.repr < repr &&
			this !in left.repr &&
			this !in right.repr &&
			repr == left.repr + {this} + right.repr &&
			values == left.values + [info] + right.values &&
			left.is_valid() &&
			right.is_valid() &&
			// if left.height > right.height then
			// 	height == left.height + 1
			// else
			// 	height == right.height + 1
			alg_tree == Node(left.alg_tree, info, right.alg_tree)
		))
	}
	method max_in_tree() returns (r: int)
		requires is_valid()
		ensures forall e :: e in values ==> e <= r
		ensures is_valid()
		decreases repr
	{
		r := info;
		if left != null {
			var max_l := left.max_in_tree();
			if max_l > r { r := max_l; }
		}
		if right != null {
			var max_r := right.max_in_tree();
			if max_r > r { r := max_r; }
		}
	}
}
