method Main() {
	var a: array<int> := new int[5];	
	a[0],a[1],a[2],a[3],a[4]:= 3,8,5,-1,7;
	print "Before sorting: ";
	print a[..];
	PairInsertionSort(a);
	assert Sorted(a[..]);
	print "\nAfter sorting: ";
	print a[..];
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

// TODO: re-develop here in Dafny Yannick Moy's SPARK Platinum-level version of the pair insertion sort algorithm that we have reviewed in class.
// In performing the re-development, please pay attention to the differences between SPARK and Dafny, as discussed in class,
// rephrasing for example the loop invariants accordingly, and using multiple-assignments where appropriate (for example when swapping two elements of the given array).
// Beyond these small differences, please keep the algorithm as similar as possible to Yannick's.
//
// Here's again Yannick's blog post https://blog.adacore.com/verifythis-challenge-in-spark
// and his complete SPARK implementation can be found here:
// https://github.com/AdaCore/spark2014/tree/master/testsuite/gnatprove/tests/pair_insertion_sort
//
// In the Dafny version it will be interesting to see how the support for multisets simplifies and shortens the proof.
//
// In this exercise you are NOT expected to document the steps of refinement
method PairInsertionSort(a: array<int>)
	ensures Sorted(a[..])
	ensures multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
	ghost var A := multiset(a[..]);
	var i: nat, j: int, x: int, y: int;
	i := 0;
	while i < a.Length - 1
		invariant Inv1(a[..], i, A)
		decreases a.Length - i
	{
		x,y := a[i], a[i+1];
		if x < y
		{
			x,y := y,x;
		}
		
		j := i - 1;
		while j >= 0 && a[j] > x
			invariant Inv2(a[..], i, j, A, x, y)
			decreases j
		{
			a[j], a[j+2], j := a[j+2], a[j], j-1;
		}

		if a[j+2] != x
		{
			a[j+1], a[j+2] := a[j+2], a[j+1];
		}

		while j >= 0 && a[j] > y
			invariant Inv3(a[..], i, j, A, y)
			decreases j
		{
			a[j], a[j+1], j := a[j+1], a[j], j-1;
		}

		i := i + 2;				
	}

	if i == a.Length-1
	{
		y, j := a[i], i-1;
		while j >=0 && a[j] > y
			invariant Inv4(a[..], i, j, A, y)
			decreases j
		{
			a[j], a[j+1], j := a[j+1], a[j], j-1;
		}
	}	
}

predicate Inv1(q: seq<int>, i: nat, A: multiset<int>)
{
	i <= |q| && Sorted(q[..i]) && multiset(q) == A
}

predicate Inv2(q: seq<int>, i: nat, j: int, A: multiset<int>, x:int,y:int)
{
	j >= -1 && j < i < |q|-1 && 
	SortedExceptAt(q[..i+2], j+1, j+2) &&
	(forall k :: j+2 < k <= i+1 ==> x < q[k]) &&
	multiset(q) == A && 
	x >= y &&
	( (q[j+1] == x && q[j+2] == y) || (q[j+1] == y && q[j+2] == x) ) 
}

predicate SortedExceptAt(q: seq<int>, l: nat, r: nat)
{
	forall i,j :: 0 <= i <= j < |q| && i != l && i != r && j != l && j != r ==> q[i] <= q[j]
}

predicate Inv3(q: seq<int>, i: nat, j: int, A: multiset<int>, y: int)
{
	j >= -1 && j < i < |q|-1 && 
	SortedExceptAt(q[..i+2], j+1, j+1) &&
	(forall k :: j+1 < k <= i+1 ==> y <= q[k]) &&
	multiset(q) == A &&
	q[j+1] == y
}

predicate Inv4(q: seq<int>, i: nat, j: int, A: multiset<int>, y: int)
{
	j >= -1 && j < i == |q|-1 && 
	SortedExceptAt(q[..i+1], j+1, j+1) &&
	(forall k :: j+1 < k <= i ==> y <= q[k]) &&
	multiset(q) == A &&
	y == q[j+1]
}