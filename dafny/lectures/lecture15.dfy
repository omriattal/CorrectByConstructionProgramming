predicate Sorted(q: seq<int>)
{
    forall i,j :: 0<=i<=j <|q| ==> q[i] == q[j]

}
function method LeftChild(i: nat) : nat {2*i + 1}
function method RightChild(i: nat) : nat {2*i + 2}

predicate RootIndex(i:nat) {i==0}

function Parent(i:nat):nat requires !RootIndex(i) {(i-1)/2}

/**
 We need the value of j-i decreases in each call, and j-i >= 0
 */
predicate AncestorIndex(i:nat,j:nat) decreases j-i
{
    i == j || (j > 2*i && AncestorIndex(i,Parent(j)))
    //  i == j || (j>2*i && assert (0<= Parent(j) < j;  AncestorIndex(i,Parent(j)))
}

predicate hp(q : seq<int>) {
    forall i,j :: 0 <= i <= j < |q| && AncestorIndex(i,j) ==> q[i] > q[j]
}
/**
An example of proof by induction
 */
lemma RootLemma(i:nat)
    ensures AncestorIndex(0,i)
    decreases i
    {
        if RootIndex(i)
        {
            assert i == 0;
            assert AncestorIndex(0,0);
        }
        else
        {
            assert !RootIndex(i);
            assert i>0;
            //induction hypothesis
            // assert forall i' :: 0<=i'<i ==> AncestorIndex(0,i');
            //and more specifiaclly, for i' being the parent of i
            assert forall i' :: 0<=i'<i ==> AncestorIndex(0,i') by {
                forall i' | 0<=i'<i ensures AncestorIndex(0,i') {RootLemma(i');}
            }
            //The above assertion is not needed, dfny already knows it.
            assert AncestorIndex(0,Parent(i)) by {
                //the conclusion of the recursive call to this lemma
                RootLemma(Parent(i));
                //and this is why the recursive call was justifiable: the parent of i is included in the induction hypothesis
                assert 0<= Parent(i) < i;
                // technically, the variant of the recursive lemma is indeed decreased at each call,
                //avoiding non termination
            }
        }

    }

lemma ProperAncestor(i:nat,j:nat)
    requires AncestorIndex(i,j) && i!=j
    ensures AncestorIndex(LeftChild(i),j) || AncestorIndex(RightChild(i),j)
    {}

//helps to avoid Dafny's no terms to trigger on warning
predicate InRange(start:nat,i:nat,end:nat) { start <= i < end}
function IndexSet(start:nat,end:nat):set<nat> { set i: nat | i < end && InRange(start,i,end)}
predicate hp_except_at(q:seq<int>,k:nat)
{
    ph(q,IndexSet(0,|q|) - {k})
}
predicate ph(q:seq<int>, indices: set<int>)
    requires forall i:: i in indices ==> i < |q|
    {
        forall i,j :: i in indices && j in indices && AncestorIndex(i,j) ==> q[i] > q[j]
    }
method HeapSort(a:array<int>)
    ensures Sorted(a[..]) && multiset(a[..]) == multiset(old(a[..]))
    modifies a
    {
        ghost var A := multiset(a[..]);
        HeapSort1(a,A);
        assert A == old(multiset(a[..]));
    }
method HeapSort1(a:array<int>, ghost A:multiset<int>)
    requires multiset(a[..]) == A
    ensures Sorted(a[..]) && multiset(a[..]) == A
    modifies a
    {
        MakeHeap(a,A);
        Sort(a,A);
    }
method MakeHeap(a:array<int>, ghost A:multiset<int>)
    requires multiset(a[..]) == A
    ensures hp(a[..]) && multiset(a[..]) == A
    modifies a
//TODO: complete, reusing the heapify operation.

predicate Inv1(q:seq<int>, i:nat, A:multiset<int>)
{
    i <= |q| && hp(q[..i]) && Sorted(q[i..]) && multiset(q) == A
}

method Sort(a:array<int>, ghost A:multiset<int>)
    requires multiset(a[..]) == A
    ensures Sorted(a[..]) && multiset(a[..]) == A
    modifies a
    {
        var i: nat := a.Length;
        while i!=0
            invariant Inv1(a[..],i,A)
            decreases i
        {
                i := i-1;
                a[0],a[i] := a[i],a[0];
                Heapify(a,i,0,A);
        }
    }
    /**
    We can't send a[1..] since it is an entirely different heap!
    We need to specify - All is heap except a position.
     */
    method Heapify(a: array<int>, heapsize:nat,j:nat,ghost A: multiset<int>)
        requires j < heapsize <= a.Length && hp_except_at(a[..heapsize],j) && multiset(a[..]) == A
        ensures  Inv1(a[..],heapsize, A)
        modifies a