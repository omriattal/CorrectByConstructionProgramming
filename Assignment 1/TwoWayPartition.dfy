method TwoWayPartition'(a: array<int>)
    requires ZeroesAndOnesOnly(a[..])
	ensures Sorted(a[..])
	ensures multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
    ghost var A := multiset(a[..]);
    var i, j := 0, 0;

    while j != a.Length    
        invariant Inv(a[..], A, i, j)
        decreases a.Length-j
    {
        if a[j]==0
        {
            a[i], a[j], i, j := a[j], a[i], i+1, j+1;
        }
        else
        {
            j := j+1;
        }
    }
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

predicate ZeroesAndOnesOnly(q: seq<int>)
{
	forall i :: 0 <= i < |q| ==> q[i] == 0 || q[i] == 1
}

predicate ZeroesOnly(q: seq<int>)
{
	forall i :: 0 <= i < |q| ==> q[i] == 0
}

predicate OnesOnly(q: seq<int>)
{
	forall i :: 0 <= i < |q| ==> q[i] == 1
}

predicate Inv(q: seq<int>, A: multiset<int>, i: nat, j: nat)
{
    i<=j<=|q| && ZeroesOnly(q[..i]) && OnesOnly(q[i..j]) && multiset(q) == A && ZeroesAndOnesOnly(q)
}

predicate method Guard(a: array<int>,ghost A: multiset<int>, i:nat, j:nat)
    requires Inv(a[..], A, i, j)
	reads a
{
    j != a.Length    
}

// implement with linear worst-case time complexity (in the length of the array)
method TwoWayPartition(a: array<int>)
	requires ZeroesAndOnesOnly(a[..])
	ensures Sorted(a[..])
	ensures multiset(a[..]) == multiset(old(a[..]))
	modifies a
{   
    // introduce logical constant
    ghost var A := multiset(a[..]);
    TwoWayPartition0(a, A);
}

method TwoWayPartition0(a: array<int>, ghost A: multiset<int>)
    requires ZeroesAndOnesOnly(a[..]) && A == multiset(a[..])
	ensures Sorted(a[..]) && multiset(a[..]) == multiset(old(a[..]))
	modifies a
{
    // strengthen postcondition
    // ghost var q := a[..];// pre with substitution of the contents of "a" with the initial contents (backed-up in "q")
    // TwoWayPartition1(a, A);
    // LemmaStrengthen(a, q, A);// "q" here acts as backup for "old(a[..])"

    TwoWayPartition1(a, A);
    LemmaStrengthen(a, A);// "q" here acts as backup for "old(a[..])"
}

lemma LemmaStrengthen(a: array<int>, A: multiset<int>)
    requires Sorted(a[..]) && multiset(a[..]) == A
    ensures Sorted(a[..]) && multiset(a[..]) == multiset(old(a[..]))
{}


// lemma LemmaStrengthen(a: array<int>, q: seq<int>, A: multiset<int>)
//     requires A == multiset(q)
//     requires Sorted(a[..]) && multiset(a[..]) == A
//     ensures Sorted(a[..]) && multiset(a[..]) == multiset(old(a[..]))
// {}

method TwoWayPartition1(a: array<int>, ghost A: multiset<int>)
    requires ZeroesAndOnesOnly(a[..]) && A == multiset(a[..])
	ensures Sorted(a[..]) && multiset(a[..]) == A
	modifies a
{
    // Introduce Local Variable *2
	var i, j;
    i, j := TwoWayPartition2(a, A);
}

method TwoWayPartition2(a: array<int>, ghost A: multiset<int>) returns(i: nat, j: nat)
    requires ZeroesAndOnesOnly(a[..]) && A == multiset(a[..]) //pre
	ensures Sorted(a[..]) && multiset(a[..]) == A //post
	modifies a
{
    // sequential composition + strengthen postcondition
	i, j := Init(a, A);
	i, j := Loop(a,A,i,j);
    LemmaStrengthenPostcondition(a, A, i, j);
}

lemma LemmaStrengthenPostcondition(a: array<int>,A: multiset<int>, i:nat, j:nat)
    requires Inv(a[..], A, i, j) && !Guard(a, A, i, j) //post'
    ensures Sorted(a[..]) && multiset(a[..]) == A //post
{}

lemma LemmaInit(a: array<int>, A: multiset<int>)
    requires ZeroesAndOnesOnly(a[..]) && A == multiset(a[..])
    ensures Inv(a[..], A, 0, 0)
{}

method Init(a: array<int>, ghost A: multiset<int>) returns(i: nat, j: nat)
    requires ZeroesAndOnesOnly(a[..]) && A == multiset(a[..]) //pre
    ensures Inv(a[..], A, i, j) //mid
{
    // assignment
    LemmaInit(a, A);
    i, j := 0, 0;
}

method Loop(a: array<int>, ghost A: multiset<int>, i0: nat, j0: nat) returns(i: nat, j: nat)
    requires Inv(a[..], A, i0, j0) //mid
    ensures Inv(a[..], A, i, j) && !Guard(a, A, i, j) //post'
    modifies a
{
    i, j := i0, j0;
    // iteration
    while Guard(a, A, i, j)
        invariant Inv(a[..], A, i, j)
        decreases a.Length-j
    {
        i, j := LoopBody(a, A, i, j);
    }
}

method LoopBody(a: array<int>, ghost A: multiset<int>, i0: nat, j0: nat) returns(i: nat, j: nat)
    requires Inv(a[..], A, i0, j0) && Guard(a, A, i0, j0)
    ensures Inv(a[..], A, i, j) && 0 <= a.Length-j < a.Length-j0
    modifies a
{
    i,j := i0,j0;
    // alternation
    if a[j]==0
    {
        i, j := LoopAssignment1(a, A, i, j);
    }
    else
    {
        // contract frame
        j := LoopAssignment2(a, A, i, j);
    }
    
}
method LoopAssignment1(a: array<int>, ghost A: multiset<int>, i0: nat, j0: nat) returns (i:nat, j:nat)
    requires Inv(a[..], A, i0, j0) && Guard(a, A, i0, j0) && a[j0]==0
    ensures Inv(a[..], A, i, j) && 0 <= a.Length-j < a.Length-j0
    modifies a
{
    i, j := i0, j0;
    // assignment
    LemmaLoopAssignment1(a, A ,i ,j);
    a[i], a[j], i, j := a[j], a[i], i+1, j+1;
}

lemma LemmaLoopAssignment1(a: array<int>, A: multiset<int>, i: nat, j: nat)
    requires Inv(a[..], A, i, j) && Guard(a, A, i, j) && a[j]==0
    ensures Inv(a[..][i := a[j]][j := a[i]], A, i+1, j+1) && 0 <= a.Length-(j+1) < a.Length-j // sequence substitution
{} 
 

method LoopAssignment2(a: array<int>, ghost A: multiset<int>, i: nat, j0: nat) returns(j: nat)
    requires Inv(a[..], A, i, j0) && Guard(a, A, i, j0) && a[j0]!=0
    ensures Inv(a[..], A, i, j) && 0 <= a.Length-j < a.Length-j0
{
    j := j0;
    // assignment
    LemmaLoopAssignment2(a, A ,i ,j);
    j := j + 1;
}

lemma LemmaLoopAssignment2(a: array<int>, A: multiset<int>, i: nat, j: nat)
    requires Inv(a[..], A, i, j) && Guard(a, A, i, j) && a[j]!=0
    ensures Inv(a[..], A, i, j+1) && 0 <= a.Length-(j+1) < a.Length-j
{}

method Main() {
	var a := new int[5];
	a[0], a[1], a[2], a[3], a[4] := 1, 0, 1, 0, 1;
	print "Before: ";
	print a[..]; 
	TwoWayPartition(a);
	print "\nAfter: ";
	print a[..]; 
}