include "HeapSort-without-Main.dfy"

// implement using a loop
method HeapIncreaseKey(a: array<int>, i: nat, key: int)
	requires i < a.Length && a[i] < key
	requires hp(a[..])
	ensures hp(a[..])
	ensures multiset(a[..]) == multiset(old(a[..])[i := key])
	modifies a
{
	// introduce logical constant
	ghost var A := a[..];
	HeapIncreaseKey1(a, A, i, key);
}

method HeapIncreaseKey1(a: array<int>, ghost A: seq<int> ,i: nat, key: int)
	requires i < a.Length && a[i] < key && hp(a[..]) && A == a[..] //pre
	ensures hp(a[..]) && multiset(a[..]) == multiset(old(a[..])[i := key]) //post
	modifies a
{
	// strengthen postcondition
    ghost var q := a[..];
    HeapIncreaseKey2(a, A,i,key);
    LemmaStrengthen1(a, q, A, i, key);
}

lemma LemmaStrengthen1(a: array<int>, q: seq<int>, A: seq<int>,i: nat, key: int)
	requires i < |q| && q[i] < key && hp(q) && A == q //pre[w\w0]
	requires hp(a[..]) && multiset(a[..]) == multiset(A[i := key]) //post'
	ensures hp(a[..]) && multiset(a[..]) == multiset(q[i := key]) //post
{}
method HeapIncreaseKey2(a: array<int>, ghost A: seq<int> ,i: nat, key: int)
	requires i < a.Length && a[i] < key && hp(a[..]) && A == a[..] //pre
	ensures hp(a[..]) && multiset(a[..]) == multiset(A[i := key])//post'
	modifies a
{
	// introduce local variable + stengthen postcondition
	var j;
	j := HeapIncreaseKey3(a, A, i, key);
	LemmaStrengthen2(a, A, i, key, j);
}
lemma LemmaStrengthen2(a: array<int>, A: seq<int>,i: nat, key: int, j: nat)
	requires j <= i < a.Length == |A| && hp(a[..]) && multiset(a[..]) == multiset(A[i := key])//post''
	ensures hp(a[..]) && multiset(a[..]) == multiset(A[i := key])//post'
{}

method HeapIncreaseKey3(a: array<int>, ghost A: seq<int> ,i: nat, key: int) returns(j: nat)
	requires i < a.Length && a[i] < key && hp(a[..]) && A == a[..]//pre
	ensures j <= i < a.Length == |A| && hp(a[..]) && multiset(a[..]) == multiset(A[i := key])//post''
	modifies a
{
	// sequential composition + stengthen postcondition
	j := HeapIncreaseKey4(a, A, i, key);
	j := HeapIncreaseKey5(a, A, i, key, j);
	LemmaStrengthen3(a, A, i, key, j);
}

lemma LemmaStrengthen3(a: array<int>, A: seq<int> ,i: nat, key: int, j: nat)
	requires Inv(a[..], A, i, key, j) && !Guard(a[..], j)//post'''
	ensures j <= i < a.Length == |A| && hp(a[..]) && multiset(a[..]) == multiset(A[i := key])//post''
{}

method HeapIncreaseKey4(a: array<int>, ghost A: seq<int> ,i: nat, key: int) returns(j: nat)
	requires i < a.Length && a[i] < key && hp(a[..]) && A == a[..]//pre
	ensures Inv(a[..], A, i, key, j)//mid
	modifies a
{
	// assignment
	LemmaAssignment2(a, A, i, key);
	j,a[i] := i,key;
}

lemma LemmaAssignment2(a: array<int>, A: seq<int> ,i: nat, key: int)
	requires i < a.Length && a[i] < key && hp(a[..]) && A == a[..] 
	ensures Inv(a[..][i := key], A, i, key, i)
{}

predicate method Guard(a: seq<int>, j: nat)
	requires j < |a|
{
	0 < j && a[j] > a[Parent(j)] 
} 

predicate Inv(a: seq<int>, A: seq<int> ,i:nat, key:int, j: nat)
{
	j <= i < |a| == |A| && hp_except_at(a, j) && hi(a, 0, |a|, j) && multiset(a) == multiset(A[i := key])
}

method HeapIncreaseKey5(a: array<int>, ghost A: seq<int> ,i: nat, key: int, j0: nat) returns(j: nat)
	requires Inv(a[..], A, i, key, j0)//mid
	ensures Inv(a[..], A, i, key, j) && !Guard(a[..], j)//post'''
	modifies a
{
	j := j0;
	// iteration
	while Guard(a[..], j)
		invariant Inv(a[..], A, i, key, j)
		decreases j
	{
		j := LoopBody(a, A, i, key, j);
	}
}

method LoopBody(a: array<int>, ghost A: seq<int> ,i: nat, key: int, j0: nat) returns(j: nat)
	requires Inv(a[..], A, i, key, j0) && Guard(a[..], j0)
	ensures Inv(a[..], A, i, key, j) && 0 <= j < j0
	modifies a
	{
		j := j0;
		// assignment
		Lemma3Assignments(a[..], A, i, key, j);
		a[j], a[Parent(j)], j := a[Parent(j)], a[j], Parent(j);
		// Q5: how does multi-variables assignment work? we found that the order of the assignments can make difference
		//j, a[j], a[Parent(j)] := Parent(j), a[Parent(j)], a[j];
	}

lemma Lemma3Assignments(a: seq<int>, A: seq<int> ,i: nat, key: int, j: nat) 
	requires Inv(a, A, i, key, j) && Guard(a, j)
	ensures Inv(a[j := a[Parent(j)]][Parent(j) := a[j]], A, i, key, Parent(j)) && 0 <= Parent(j) < j
{
	var a_sub := a[j := a[Parent(j)]][Parent(j) := a[j]];
	// postconditions:
	// Parent(j) < j <= i < |a| == |A|             post1
	// hp_except_at(a_sub , Parent(j)) 			   post2
	// hi(a_sub, 0, |a|, Parent(j))                post3
	// multiset(a_sub) == multiset(A[i := key])    post4
	// 0 <= Parent(j) < j						   post5

	// Dafny can undersatand these postcondition without proof:
	assert Parent(j) < j <= i < |a| == |A|;			 //post1
	assert hi(a_sub, 0, |a|, Parent(j));	         //post3
	assert multiset(a_sub) == multiset(A[i := key]); //post4
	assert 0 <= Parent(j) < j;					     //post5

	// But Dafny failed to understand that post2 is true
	// We will help Dafny to understand that post2 is also true by the following proof:
	assert hp_except_at(a_sub , Parent(j)) by {		 
		var indices := IndexSet(0, |a_sub|) - {Parent(j)};
		forall r:nat,k:nat | r in indices && k in indices && AncestorIndex(r, k) ensures a_sub[r] >= a_sub[k]
		{
			// Due to case analysis we inferred that Dafny needed some help only with a single case in which r == j:
			if(r == k)
			{
				assert a_sub[r] >= a_sub[k];
			}
			else if(r != j && k != j)
			{	
				assert a_sub[r] >= a_sub[k];
			}
			else if r == j
			{// 
				assert hp_except_at(a, j);						//Before subtitution: a[Parent(j)] > a[k] s.t AncestorIndex(Parent(j), k)
				assert AncestorIndex(Parent(j),r);				//Because AncestorIndex(Parent(j),j) && r == j
				assert AncestorIndex(r, k);						//Because of the forall assumption
				AncestorIndexTransitive(Parent(j), r, k);		//We had to convince Dafny AncestorIndex is a transitive relation
				assert AncestorIndex(Parent(j),k);				//Because AncestorIndex is a transitive relation
				assert a[Parent(j)] >= a[k];					//We saw it on the first step, can be inferred from hp_except_at(a, j)  

				assert a_sub == a[..][j := a[Parent(j)]][Parent(j) := a[j]]; //definition of a_sub
				assert a_sub[j] == a_sub[r] >= a_sub[k];		//a[Parent(j)] == a_sub[j] == a_sub[r] >= a[k] 
				assert a_sub[r] >= a_sub[k];					//now we got what we need 
			}
			else // k == j 
			{
				assert a_sub[r] >= a_sub[k];
			}
		}
	}        

}

lemma AncestorIndexTransitive(a:nat, b:nat, c:nat)
	requires AncestorIndex(a,b) && AncestorIndex(b,c)
	ensures AncestorIndex(a,c)
{}

/**********************************************************************************************************************/

// implement using recursion
method HeapIncreaseKey_with_Recursion(a: array<int>, i: nat, key: int)
	requires i < a.Length && a[i] < key
	requires hp(a[..])
	ensures hp(a[..])
	ensures multiset(a[..]) == multiset(old(a[..])[i := key])
	modifies a
	
{
	// introduce logical constant
    ghost var A := a[..];
    HeapIncreaseKey_with_Recursion1(a, A, i, key);
}

method HeapIncreaseKey_with_Recursion1(a: array<int>, ghost A: seq<int>, i: nat, key: int)
	requires i < a.Length && a[i] < key && hp(a[..]) && A == a[..]//pre
	ensures hp(a[..]) && multiset(a[..]) == multiset(old(a[..])[i := key])//post
	modifies a
{
	// strengthen postcondition
	ghost var q := a[..];
	HeapIncreaseKey_with_Recursion2(a, A, i, key);
	LemmaStrengthen4(a, A, q, i, key);
}

lemma LemmaStrengthen4(a: array<int>, A: seq<int>, q: seq<int>, i: nat, key: int)	
	requires i < |q| && q[i] < key && hp(q) && A == q //pre[w\w0]
	requires hp(a[..]) && multiset(a[..]) == multiset(A[i := key])//post'
	ensures hp(a[..]) && multiset(a[..]) == multiset(q[i := key])//post
{}

method HeapIncreaseKey_with_Recursion2(a: array<int>, ghost A: seq<int>, i: nat, key: int)
	requires i < a.Length && a[i] < key && hp(a[..]) && A == a[..]//pre
	ensures hp(a[..]) && multiset(a[..]) == multiset(A[i := key])//post'
	modifies a
{
	// Introduce Local Variable
	var j;
	j := HeapIncreaseKey_with_Recursion3(a, A, i, key);
}

method HeapIncreaseKey_with_Recursion3(a: array<int>, ghost A: seq<int>, i: nat, key: int) returns(j: nat)
	requires i < a.Length && a[i] < key && hp(a[..]) && A == a[..]
	ensures hp(a[..]) && multiset(a[..]) == multiset(A[i := key])
	modifies a
{
	// sequential composition + weaken precondition
	j := init(a, A, i, key);
	LemmaWeaken(a, A, i, key, j);
	j := HeapIncreaseKey_with_Recursion4(a, A, i, key, j);
}

method init(a: array<int>, ghost A: seq<int>, i: nat, key: int) returns(j: nat)
	requires i < a.Length && a[i] < key && hp(a[..]) && A == a[..]//pre
	ensures  j <= i < a.Length == |A| && hp_except_at(a[..],j) && multiset(a[..]) == multiset(A[i := key]) && hi(a[..],0,a.Length, j)//mid
	modifies a
{
	// assignment
	LemmaAssignment(a, A, i, key);
	j, a[i] := i, key;
}

lemma LemmaAssignment(a: array<int>, A: seq<int>, i: nat, key: int)
	requires i < a.Length && a[i] < key && hp(a[..]) && A == a[..]
	ensures i <= i < a.Length == |A| && hp_except_at(a[..][i := key],i) && multiset(a[..][i := key]) == multiset(A[i := key]) && hi(a[..][i := key],0,a.Length, i)
{}

lemma LemmaWeaken(a: array<int>, A: seq<int>, i: nat, key: int, j: nat)
	requires j <= i < a.Length == |A| && hp_except_at(a[..],j) && multiset(a[..]) == multiset(A[i := key]) && hi(a[..],0,a.Length, j)//mid
	ensures Inv(a[..], A, i, key, j)//mid'
{}

// This is the recursion part:
method HeapIncreaseKey_with_Recursion4(a: array<int>, ghost A: seq<int>, i: nat, key: int, j0: nat) returns(j: nat)
	requires Inv(a[..], A, i, key, j0)//mid'
	ensures hp(a[..]) && multiset(a[..]) == multiset(A[i := key])
	modifies a
	decreases j0, 10
{
	j := j0;
	// alternation + skip command
	if Guard(a[..], j)
	{
		j := HeapIncreaseKey_with_Recursion5(a, A, i, key, j);
	}
	else
	{
		LemmaSkip(a, A, i, key, j);
	}
}

lemma LemmaSkip(a: array<int>, A: seq<int>, i: nat, key: int, j: nat)
	requires Inv(a[..], A, i, key, j) && !Guard(a[..], j)
	ensures hp(a[..]) && multiset(a[..]) == multiset(A[i := key])
{}

method HeapIncreaseKey_with_Recursion5(a: array<int>, ghost A: seq<int>, i: nat, key: int, j0: nat) returns(j: nat)
	requires Inv(a[..], A, i, key, j0) && Guard(a[..], j0)
	ensures hp(a[..]) && multiset(a[..]) == multiset(A[i := key])
	modifies a
	decreases j0, 9
{
	j := j0;
	// sequential composition + weaken precondition + strengthen postcondition 
	j := Assignments(a, A, i, key, j0);
	LemmaPre(a, A, i, key, j0, j);
	assert j == Parent(j0) < j0; // termination justification
	j := HeapIncreaseKey_with_Recursion4(a, A, i, key, j);
	LemmaPost(a, A, i, key, j0, j);
}
lemma LemmaPre(a: array<int>, A: seq<int>, i: nat, key: int, j0: nat, j: nat)
	requires Inv(a[..], A, i, key, j) //&& j == Parent(j0) // postcondition of Assignments == precondition of the rec call (mid of the seq comp)
	ensures Inv(a[..], A, i, key, j) //[j\j0]
{
	// Q1: can we delete j == Parent(j0) to avoid errors? Do we have to justify it using another weaken precondition lemma?
	// Q2: is the subtitution [j\j0] is right?
}

lemma LemmaPost(a: array<int>, A: seq<int>, i: nat, key: int, j0: nat, j: nat)
	requires Inv(a[..], A, i, key, j0) // precondition of HeapIncreaseKey_with_Recursion4 with subtitution [j\j0]
	requires hp(a[..]) && multiset(a[..]) == multiset(A[i := key]) // postcondition of HeapIncreaseKey_with_Recursion4
	ensures hp(a[..]) && multiset(a[..]) == multiset(A[i := key])  // postcondition of HeapIncreaseKey_with_Recursion5
{
	// Q3: good enough?
}

// method HeapIncreaseKey_with_Recursion4(a: array<int>, ghost A: seq<int>, i: nat, key: int, j0: nat) returns(j: nat)
// 	requires Inv(a[..], A, i, key, j0)//mid'
// 	ensures hp(a[..]) && multiset(a[..]) == multiset(A[i := key])
// 	modifies a
// 	decreases j0, 10

method Assignments(a: array<int>, ghost A: seq<int>, i: nat, key: int, j0: nat) returns(j: nat)
	requires Inv(a[..], A, i, key, j0) && Guard(a[..], j0)
	ensures Inv(a[..], A, i, key, j) && j == Parent(j0)
	modifies a
	decreases j0
{
	j := j0;
	// assignment
	LemmaAssignments(a, A, i, key, j);
	a[j], a[Parent(j)], j := a[Parent(j)], a[j], Parent(j);
}

lemma LemmaAssignments(a: array<int>, A: seq<int>, i: nat, key: int, j: nat) 
	requires Inv(a[..], A, i, key, j) && Guard(a[..], j)
	ensures Inv(a[..][j := a[Parent(j)]][Parent(j) := a[j]], A, i, key, Parent(j)) && Parent(j) == Parent(j)
{
	// We have riched to the same problem as in the iterative function, but now we already have the solution - Lemma3Assignments
	assert Inv(a[..][j := a[Parent(j)]][Parent(j) := a[j]], A, i, key, Parent(j)) by{
		// Q4: can we use lemma this way? do we have to fustify it?
		Lemma3Assignments(a[..], A, i, key, j);
	}
}
 
/**********************************************************************************************************************/

method {:verify false} Main() {
	var a: array<int> := new int[5];
	a[0], a[1], a[2] := 4, 8, 6;

	 var q0: seq<int> := a[..];
	assert q0 == [4,8,6];
	HeapSort(a);
	assert multiset(a[..]) == multiset(q0);
	print "the sorted version of [4, 8, 6] is ";
	print a[..];
	assert Sorted(a);
	assert a[..] == [4,6,8];

	a := new int[5];
	a[0], a[1], a[2], a[3], a[4] := 3, 8, 5, -1, 10;
	q0 := a[..];
	assert q0 == [3, 8, 5, -1, 10];
	HeapSort(a);
	assert multiset(a[..]) == multiset(q0);
	print "\nthe sorted version of [3, 8, 5, -1, 10] is ";
	print a[..];
	assert Sorted(a);
	assert a[..] == [-1, 3, 5, 8, 12];

	a[0], a[1], a[2], a[3], a[4] := 3, 8, 5, -1, 12;
	ghost var A := multiset(a[..]);
	MakeHeap(a, A);
	assert hp(a[..]);
	print "\nthe heap before increasing keys is ";
	print a[..];
	// a[..] == [12, 8, 5, -1, 3];
	ghost var q1 := a[..];
	HeapIncreaseKey(a, 3, 9);
	assert hp(a[..]);
	print "\nthe heap after increasing element 3 to 9 is ";
	print a[..];
	assert a[..] == [12, 9, 5, 8, 3];
	assert multiset(a[..]) == multiset(q1[3 := 9]); // == multiset([12, 9, 5, 8, 3]);
	
	ghost var q2 := a[..];
	HeapIncreaseKey_with_Recursion(a, 4, 11);
	assert hp(a[..]);
	print "\nthe heap after increasing element 4 to 11 is ";
	print a[..];
	assert a[..] == [12, 11, 5, 8, 9];
	assert multiset(a[..]) == multiset(q2[4 := 11]); // == multiset([12, 11, 5, 8, 9]);

	assert AncestorIndex(0,0);
	assert AncestorIndex(0,1);
	assert AncestorIndex(0,2);
	assert AncestorIndex(0,3); // <0,1,3>
	assert AncestorIndex(0,4); // <0,1,4>
	assert !AncestorIndex(1,0);
	assert AncestorIndex(1,1);
	assert !AncestorIndex(1,2);
	assert AncestorIndex(1,3);
	assert AncestorIndex(1,4);
	assert !AncestorIndex(2,0);
	assert !AncestorIndex(2,1);
	assert AncestorIndex(2,2);
	assert !AncestorIndex(2,3);
	assert !AncestorIndex(2,4);
	assert AncestorIndex(2,5);
	assert AncestorIndex(2,6);
	
}