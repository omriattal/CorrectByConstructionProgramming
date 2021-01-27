// R. Ettinger, December 2020, following Carroll Morgan's development in "Programming from Specifications", in Dafny v2.3.0
// [this version has no Main method; it is meant to be included in another program; "Parent" is now a "function method" and can be used in executable code]
method {:verify false} HeapSort'(a: array<int>)
	ensures Sorted(a) && multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
	var i := a.Length/2;
	while i != 0
	{
		i := i-1;
		Heapify'(a, i, a.Length);
	}
	if a.Length > 1
	{
		var i: nat := a.Length;
		while i >= 2
		{
			i := i-1;
			a[0], a[i] := a[i], a[0];
			Heapify'(a, 0, i);
		}
	}
}

method {:verify false} Heapify'(a: array<int>, l: nat, h: nat)
	requires l < h <= a.Length && ph(a[..], IndexSet(l+1, h)) && fn(a[..], h)
	ensures ph(a[..], IndexSet(l, h)) && fn(a[..], h) && multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
	var j := l;
	var left, right := LeftChild(j), RightChild(j);
	while (left < h && a[left] > a[j]) || (right < h && a[right] > a[j])
	{
		var k := if right < h && a[left] < a[right] then right else left;
		a[j], a[k] := a[k], a[j];
		j, left, right := k, LeftChild(k), RightChild(k);
	}
}

predicate Sorted(a: array<int>)
	reads a
{
	forall i,j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
}

predicate SortedSequence(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

function method LeftChild(i: nat): nat { 2*i+1 }

function method RightChild(i: nat): nat { 2*i+2 }

function method Parent(i: nat): nat requires !RootIndex(i) { (i-1)/2 }

predicate RootIndex(i: nat) { i == 0 }

predicate AncestorIndex(i: nat, j: nat) decreases j-i 
{
	i == j || (j > 2*i && AncestorIndex(i, Parent(j)))
}

// for a reason unknown to me, using a predicate such as this in set comprehension expressions
// helps to avoid Dafny's "No terms found to trigger on" warning
predicate InRange(start: nat, i: nat, end: nat) { start <= i < end }

function IndexSet(start: nat, end: nat): set<nat> { set i: nat | i < end && InRange(start, i, end) }

// definition of a heap
predicate hp(q: seq<int>)
{
	ph(q, IndexSet(0, |q|))
}

predicate hp_except_at(q: seq<int>, k: nat)
{
	ph(q, IndexSet(0, |q|) - {k})
}

// partial heap
predicate ph(q: seq<int>, indices: set<nat>)
	requires forall i :: i in indices ==> i < |q|
{
	forall i,j :: i in indices && j in indices && AncestorIndex(i, j) ==> q[i] >= q[j]
}

// element j is a valid heap element (in the given range) with respect to its ancestors (lower indices)
predicate lo(q: seq<int>, l: nat, h: nat, j: nat) //j is smaller than his parents 
	requires l <= h <= |q| && j < |q|
{
	forall i :: l <= i < h && AncestorIndex(i, j) ==> q[i] >= q[j]
}

// element j is a valid heap element (in the given range) with respect to its descendents (higher indices)
predicate hi(q: seq<int>, l: nat, h: nat, j: nat)// j is bigger than his childrens
	requires l <= h <= |q| && j < |q|
{
	forall k :: l <= k < h && AncestorIndex(j, k) ==> q[j] >= q[k]
}

// the suffix q[i..] holds elements in their final (sorted) positions
predicate fn(q: seq<int>, i: nat)//finel position - for elements located right to i 
	requires i <= |q|
{
	SortedSequence(q[i..]) &&
	forall j,k :: 0 <= j < i <= k < |q| ==> q[j] <= q[k] 
}

method HeapSort(a: array<int>)
	ensures Sorted(a) && multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
	// introduce logical constant + strengthen postcondition + sequential composition
	ghost var A := multiset(a[..]);
	MakeHeap(a, A);
	Sort(a, A);
	assert A == old(multiset(a[..])); // this way the postcondition of Sort is indeed strong enough
}

method MakeHeap(a: array<int>, ghost A: multiset<int>)
	requires multiset(a[..]) == A
	ensures hp(a[..]) && multiset(a[..]) == A
	modifies a
{
	// introduce local variable + leading assignment + weaken precondition + strengthen poscondition
	var i: nat := a.Length/2;
	// second half is trivially a partial heap as it contains leaves only
	LemmaMakeHeapPre(a, i, A);
	i := MakeHeap1(a, i, A);
	LemmaMakeHeapPost(a, i, A);
}

// proof of weaken precondition step
lemma LemmaMakeHeapPre(a: array<int>, i: nat, A: multiset<int>)
	requires i == a.Length/2 && multiset(a[..]) == A // precondition of MakeHeap + the initialization
	ensures i <= a.Length/2 && ph(a[..], IndexSet(i, a.Length)) && multiset(a[..]) == A // precondition of MakeHeapLoop
{}

// proof of the strengthen postcondition
lemma LemmaMakeHeapPost(a: array<int>, j: nat, A: multiset<int>)
	requires 0 == j <= a.Length / 2 && ph(a[..], IndexSet(j, a.Length)) && multiset(a[..]) == A
	ensures	hp(a[..]) && multiset(a[..]) == A // postcondition of MakeHeap
{
	// indeed, the definition of a heap ("hp") is in terms of a partial heap ("ph") for range 0..a.Length
}

method MakeHeap1(a: array<int>, i0: nat, ghost A: multiset<int>) returns (i: nat)
	requires i0 <= a.Length/2 && ph(a[..], IndexSet(i0, a.Length)) && multiset(a[..]) == A
	ensures 0 == i <= a.Length/2 && ph(a[..], IndexSet(i, a.Length)) && multiset(a[..]) == A
	modifies a
{
	i := i0;
	// iteration
	while i != 0
		invariant i <= a.Length/2 && ph(a[..], IndexSet(i, a.Length)) && multiset(a[..]) == A
		decreases i
	{
		i := MakeHeap2(a, i, A);
	}
}

method MakeHeap2(a: array<int>, i0: nat, ghost A: multiset<int>) returns (i: nat)
	requires 0 < i0 <= a.Length/2 && ph(a[..], IndexSet(i0, a.Length)) && multiset(a[..]) == A // pre[i0 \ i0-1]
	ensures i <= a.Length / 2 && ph(a[..], IndexSet(i, a.Length)) && multiset(a[..]) == A // post1[i0 \ i0-1]
	ensures i < i0 // post2[i0 \ i0-1]
	modifies a
{
	i := i0;
	// leading assignment (could combine with further steps but prefer to practice documenting this step alone)
	i := i - 1;
	i := HeapifyNode(a, i, A);
}

// pre, post1, and post2 here were inferred from the specification of MakeHeapLoopBody above by the inverse substitution:
// the "i0" was replaced by "i0+1" in the precondition and the postcondition
method HeapifyNode(a: array<int>, i0: nat, ghost A: multiset<int>) returns (i: nat)
	requires 0 < i0 + 1 <= a.Length/2 && ph(a[..], IndexSet(i0 + 1, a.Length)) && multiset(a[..]) == A // pre
	ensures i <= a.Length/2 && ph(a[..], IndexSet(i, a.Length)) && multiset(a[..]) == A // post1
	ensures i < i0 + 1 // post2
	modifies a
{
	i := i0;
	// reuse: contract frame + weaken precondition + strengthen poscondition
	LemmaHeapifyNodePre(a, i, A);
	Heapify(a, i, a.Length, A);
	LemmaHeapifyNodePost(a, i, A);
}

lemma LemmaHeapifyNodePre(a: array<int>, i: nat, A: multiset<int>)
	// precondition of HeapifyNode
	requires 0 < i+1 <= a.Length/2 && ph(a[..], IndexSet(i+1, a.Length)) && multiset(a[..]) == A
	// precondition of Heapify with [l, h \ i, a.Length]
	ensures i < a.Length <= a.Length && ph(a[..], IndexSet(i+1, a.Length)) && fn(a[..], a.Length) && multiset(a[..]) == A
{}

lemma LemmaHeapifyNodePost(a: array<int>, i: nat, A: multiset<int>)
	// from the precondition of HeapifyNode (availabe here since "i" is no longer in the frame)
	requires 0 < i+1 <= a.Length/2
	// postcondition of Heapify with [l, h \ i, a.Length]
	requires ph(a[..], IndexSet(i, a.Length)) && fn(a[..], a.Length) && multiset(a[..]) == A
	// postcondition of HeapifyNode with [i \ i0] first (contract frame) and then the "i0" is renamed everywhere back to "i"
	ensures i <= a.Length/2 && ph(a[..], IndexSet(i, a.Length)) && multiset(a[..]) == A
	ensures i < i+1
{}

method Sort(a: array<int>, ghost A: multiset<int>)
	requires hp(a[..]) && multiset(a[..]) == A
	ensures Sorted(a) && multiset(a[..]) == A
	modifies a
{
	// alternation + skip command
	if a.Length > 1
	{
		Sort1a(a, A);
	}
	else
	{
		Sort1b(a, A); // with 0 or 1 elements, the array is already sorted
	}
}

lemma Sort1b(a: array<int>, A: multiset<int>)
	requires hp(a[..]) && multiset(a[..]) == A
	requires a.Length <= 1
	ensures Sorted(a) && multiset(a[..]) == A
{}

method Sort1a(a: array<int>, ghost A: multiset<int>)
	requires hp(a[..]) && multiset(a[..]) == A
	requires a.Length > 1
	ensures Sorted(a) && multiset(a[..]) == A
	modifies a
{
	// introduce local variable + leading assignment +
	// weaken precondition (proof obligation not included) + iteration
	var i: nat := a.Length;
	while i >= 2
		invariant Inv1(a[..], i, A)
		decreases i
	{
		i := Sort2(a, i, A);
	}
}

predicate Inv1(q: seq<int>, i: nat, A: multiset<int>)
{
	1 <= i <= |q| && hp(q[..i]) && fn(q, i) && multiset(q) == A
}

method Sort2(a: array<int>, i0: nat, ghost A: multiset<int>) returns (i: nat)
	requires Inv1(a[..], i0, A) && i0 >= 2
	ensures Inv1(a[..], i, A) && i < i0
	modifies a
{
	i := i0;
	// leading assignment + contract frame
	i := i-1;
	Sort3(a, i, A);
}

method Sort3(a: array<int>, i: nat, ghost A: multiset<int>)
	requires Inv1(a[..], i+1, A) && i+1 >= 2
	ensures Inv1(a[..], i, A) // && i < i+1
	modifies a
{
	// leading assignment + weaken precondition
	a[0], a[i] := a[i], a[0];
	Lemma1(a, i, A);
	HeapifyRoot(a, i, A);
}

lemma Lemma1(a: array<int>, i: nat, A: multiset<int>)
	requires 2 <= i+1 <= a.Length && Inv1(a[..][0 := a[i]][i := a[0]], i+1, A)
	ensures 1 <= i < a.Length && hp_except_at(a[..i], 0) && fn(a[..], i) && multiset(a[..]) == A
{
	var q0 := a[..][0 := a[i]][i := a[0]];
	assert SortedSequence(q0[i+1..]);
	assert SortedSequence(a[i+1..]);
	assert forall j,k :: 0 <= j < i+1 <= k < |q0| ==> q0[j] <= q0[k];
	assert hp(q0[..i+1]);
	var q1 := a[..];
	assert SortedSequence(q1[i..]) by {
		forall m,n | i <= m <= n < |q1| ensures q1[m] <= q1[n] {
			if m == i
			{
				assert q1[m] == q0[0];
			}
		}
	}
	forall j,k | 0 <= j < i <= k < |q1| ensures q1[j] <= q1[k] {
		assert q1[i] == q0[0];
		assert q1[0] == q0[i];
		if j == 0 && k == i
		{
			assert q1[j] == q0[i] <= q0[0] == q1[k] by {
				assert hp(q0[..i+1]);
				assert AncestorIndex(0, i) by { RootLemma(); }
			}
		}
		else if j == 0
		{
			assert q1[j] <= q1[k];
		}
		else if k == i
		{
			assert q1[j] == q0[j] <= q0[0] == q1[k] by {
				assert hp(q0[..i+1]);
				assert AncestorIndex(0, j) by { RootLemma(); }
			}
		}
		else
		{
			assert q1[j] == q0[j] <= q0[k] == q1[k];
		}
	}
}

method HeapifyRoot(a: array<int>, i: nat, ghost A: multiset<int>)
	requires 1 <= i < a.Length && hp_except_at(a[..i], 0) && fn(a[..], i) && multiset(a[..]) == A
	ensures Inv1(a[..], i, A)
	modifies a
{
	// reuse: weaken precondition + strengthen postcondition
	LemmaHeapifyRootPre(a, i, A);
	Heapify(a, 0, i, A);
	LemmaHeapifyRootPost(a, i, A);
}

lemma LemmaHeapifyRootPre(a: array<int>, i: nat, A: multiset<int>)
	requires 1 <= i < a.Length && hp_except_at(a[..i], 0) && fn(a[..], i) && multiset(a[..]) == A // pre of HeapifyRoot
	ensures 0 < i <= a.Length && ph(a[..], IndexSet(1, i)) && fn(a[..], i) && multiset(a[..]) == A // pre of Heapify with [l, h \ 0, i]
{}

lemma LemmaHeapifyRootPost(a: array<int>, i: nat, A: multiset<int>)
	requires 0 < i <= a.Length // from pre of Heapify with [l, h \ 0, i] (note that l and h are not in the frame of Heapify)
	requires ph(a[..], IndexSet(0, i)) && fn(a[..], i) && multiset(a[..]) == A // post of Heapify with [l, h \ 0, i]
	ensures Inv1(a[..], i, A) // post of HeapifyRoot
{}

// "l" is the index of the element that needs fixing, "h" is the size of the heap
method Heapify(a: array<int>, l: nat, h: nat, ghost A: multiset<int>)
	requires l < h <= a.Length && ph(a[..], IndexSet(l+1, h)) && fn(a[..], h) && multiset(a[..]) == A
	ensures ph(a[..], IndexSet(l, h)) && fn(a[..], h) && multiset(a[..]) == A
	modifies a
{
	// introduce local variable + leading assignment + weaken precondition + strengthen postcondition
	var j, left, right := l, LeftChild(l), RightChild(l);
	j, left, right := Heapify1(a, l, h, j, left, right, A);
	Lemma2(a, l, h, j, left, right, A);
}

predicate Inv2(q: seq<int>, l: nat, h: nat, j: nat, left: nat, right: nat, A: multiset<int>)
{
	l <= j < h <= |q| && left == LeftChild(j) && right == RightChild(j) &&
	ph(q, IndexSet(l, h) - {j}) && lo(q, l, h, j) && fn(q, h) && multiset(q) == A
}

lemma Lemma2(a: array<int>, l: nat, h: nat, j: nat, left: nat, right: nat, A: multiset<int>)
	requires Inv2(a[..], l, h, j, left, right, A) && hi(a[..], l, h, j)
	ensures ph(a[..], IndexSet(l, h)) && fn(a[..], h) && multiset(a[..]) == A
{}

method Heapify1(a: array<int>, l: nat, h: nat, j0: nat, left0: nat, right0: nat, ghost A: multiset<int>) returns (j: nat, left: nat, right: nat)
	requires Inv2(a[..], l, h, j0, left0, right0, A)
	ensures Inv2(a[..], l, h, j, left, right, A) && hi(a[..], l, h, j)
	modifies a
{
	j, left, right := j0, left0, right0;
	// iteration (designed initially with a convenient-yet-inefficient guard and revised later with an equivalent efficient formulation)
	while HeapifyGuard(a, h, j, left, right) // !hi(a[..], l, h, j)
		invariant Inv2(a[..], l, h, j, left, right, A)
		decreases h-j
	{
		EquivalentGuards(a, l, h, j, left, right, A);
		j, left, right := SwapWithLargerChild(a, l, h, j, left, right, A);
	}
	EquivalentGuards(a, l, h, j, left, right, A);
}

predicate method HeapifyGuard(a: array<int>, h: nat, j: nat, left: nat, right: nat)
	requires j < h <= a.Length
	reads a
{
	(left < h && a[left] > a[j])	|| (right < h && a[right] > a[j])
}

lemma EquivalentGuards(a: array<int>, l: nat, h: nat, j: nat, left: nat, right: nat, A: multiset<int>)
	requires Inv2(a[..], l, h, j, left, right, A)
	ensures !hi(a[..], l, h, j) <==> HeapifyGuard(a, h, j, left, right)
{
	if right < h // both children are in the heap
	{
		calc {
			HeapifyGuard(a, h, j, left, right);
		== // by definition
			(left < h && a[left] > a[j])	|| (right < h && a[right] > a[j]);
		== { assert left < h && right < h; }
			a[left] > a[j]	|| a[right] > a[j];
		== { Lemma3a(a, l, h, j, left, right); }
			!hi(a[..], l, h, j);
		}
	}
	else if left < h // only the left child is in the heap
	{
		calc {
			HeapifyGuard(a, h, j, left, right);
		== // by definition of HeapifyGuard
			(left < h && a[left] > a[j])	|| (right < h && a[right] > a[j]);
		== { assert left < h && !(right < h); }
			a[left] > a[j];
		== { Lemma3b(a, l, h, j); }
			!hi(a[..], l, h, j);
		}
	}
	else // a leaf
	{
		assert !HeapifyGuard(a, h, j, left, right); // left and right are outside the heap (>= h)
		assert hi(a[..], l, h, j); // vacuously true, as there are no children in scope
	}
}

lemma Lemma3a(a: array<int>, l: nat, h: nat, j: nat, left: nat, right: nat)
	requires l <= j < left < right < h <= a.Length && ph(a[..], IndexSet(l, h)-{j})
	requires left == LeftChild(j) && right == RightChild(j)
	ensures !hi(a[..], l, h, j) <==> a[left] > a[j]	|| a[right] > a[j]
{
	if a[left] > a[j]	|| a[right] > a[j]
	{
		assert AncestorIndex(j, left) && AncestorIndex(j, right);
	}
	else
	{
		forall k | l <= k < h && AncestorIndex(j, k) ensures a[j] >= a[k] {
			if k != j
			{
				assert AncestorIndex(left, k) || AncestorIndex(right, k) by { ProperAncestor(j, k); }
			}
		}
	}
}

lemma Lemma3b(a: array<int>, l: nat, h: nat, j: nat)
	requires l <= j < h <= a.Length && ph(a[..], IndexSet(l, h)-{j})
	requires RightChild(j) == h
	ensures !hi(a[..], l, h, j) <==> a[LeftChild(j)] > a[j]
{
	assert AncestorIndex(j, LeftChild(j));
}

method SwapWithLargerChild(a: array<int>, l: nat, h: nat, j0: nat, left0: nat, right0: nat, ghost A: multiset<int>) returns (j: nat, left: nat, right: nat)
	requires Inv2(a[..], l, h, j0, left0, right0, A) && !hi(a[..], l, h, j0)
	ensures Inv2(a[..], l, h, j, left, right, A) && 0 <= h-j < h-j0
	modifies a
{
	j, left, right := j0, left0, right0;
	// introduce local variable + following assignment + contract frame
	var k := SwapWithLargerChild1(a, l, h, j, left, right, A);
	j, left, right := k, LeftChild(k), RightChild(k);
}

method SwapWithLargerChild1(a: array<int>, l: nat, h: nat, j: nat, left: nat, right: nat, ghost A: multiset<int>) returns (k: nat)
	requires Inv2(a[..], l, h, j, left, right, A) && !hi(a[..], l, h, j)
	ensures Inv2(a[..], l, h, k, LeftChild(k), RightChild(k), A) && 0 <= h-k < h-j
	modifies a
{
	// following assignment + contract frame (removing the "modifies a")
	k := LargerChildIndex(a, l, h, j, left, right, A);
	a[j], a[k] := a[k], a[j];
}

method LargerChildIndex(a: array<int>, l: nat, h: nat, j: nat, left: nat, right: nat, ghost A: multiset<int>) returns (k: nat)
	requires Inv2(a[..], l, h, j, left, right, A) && !hi(a[..], l, h, j)
	ensures k < h && Inv2(a[..][j := a[k]][k := a[j]], l, h, k, LeftChild(k), RightChild(k), A) && 0 <= h-k < h-j
{
	// assignment
	assert left < h; // in range, follows from !hi
	LemmaLargerChildIndex(a, l, h, j, left, right, A);
	k := GetLargerChildIndex(a, h, j, left, right);
}

// element "j" has at least one child in the heap (whose size is "h")
function method GetLargerChildIndex(a: array<int>, h: nat, j: nat, left: nat, right: nat): nat
	requires j < left < h <= a.Length && left == LeftChild(j) && right == RightChild(j)
	reads a
{
	if right < h && a[left] < a[right] then right else left
}

lemma LemmaLargerChildIndex(a: array<int>, l: nat, h: nat, j: nat, left: nat, right: nat, A: multiset<int>)
	requires Inv2(a[..], l, h, j, left, right, A) && !hi(a[..], l, h, j)
	ensures var k := GetLargerChildIndex(a, h, j, left, right);
		k < h && Inv2(a[..][j := a[k]][k := a[j]], l, h, k, LeftChild(k), RightChild(k), A) && 0 <= h-k < h-j
{
	var k := GetLargerChildIndex(a, h, j, left, right);
	var q := a[..][j := a[k]][k := a[j]];
	assert ph(q, IndexSet(l, h) - {k}) by {
		var indices := IndexSet(l, h) - {k};
		forall m,n | m in indices && n in indices && AncestorIndex(m, n) ensures q[m] >= q[n]
		{
			if m == j
			{
				assert q[m] == a[k];
				assert a[k] >= q[n] by {
					if n != j
					{
						assert AncestorIndex(left, n) || AncestorIndex(right, n) by { ProperAncestor(j, n); }
					}
				}
			}
		}
	}
}

lemma RootLemma()
	ensures forall i: nat :: AncestorIndex(0, i)
{}

lemma ProperAncestor(i: nat, j: nat)
	requires AncestorIndex(i, j) && i != j
	ensures AncestorIndex(LeftChild(i), j) || AncestorIndex(RightChild(i), j)
{}
