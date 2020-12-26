/**
ensures forall i :: 0 <= i < a.Length ==> a[i] <= a[i+1] this is not good on its own because we could have changed array's values 
and not remain with the previous ones. for example array[i] = 7
we need to add a precondition so that we'll remain with the same.
ensures forall x :: x in a[..] ==> x in old (a[..]). this is not good because we need to sum the amount of times it's in old_a and a.
ensures (set x | x in a[..]) == (set x | x in old(a[..])) - more elegant to the ensures above, but the same problem. we need multiset!
multiset is both a function and a type
 */

predicate Sorted(q: seq<int>)
{
    // we could have written i < j , doesn't matter
    forall i,j :: 0<= i <= j < |q| ==> q[i] <= q[j]
}
predicate SortedExceptAt(q: seq<int>, k: nat)
    {
        forall i,j :: 0<=i<=j < |q| && i!=k && j!=k ==> q[i] <= q[j]
    }
method InsertionSort(a: array<int>)
    requires true // pre
    ensures forall i :: 0 <= i < a.Length -1  ==> a[i] <= a[i+1] 
    ensures multiset(a[..]) == multiset(old(a[..])) // old a is the value of a in the paramters of the function. old allowed only in specification/ghost context
    modifies a // we can change a, not as in previous functions when they were not part of the frame (can't change local variables). modifies adds to frame.
    {
        //introduce logical constants
        // ghost var A:= multiset(a[..]);
        ghost var A :| A == multiset(a[..]); // :| is a such that, give me a value of A, such that A == multiset... the same as the assignment above. this is what the law expect (such that)
        InsertionSort1(a,A);

    }
    /**
    Adding ghost to function parameters is only for proving correctness. the compiled version will not show up in running time
     */
method InsertionSort1(a:array<int>, ghost A: multiset<int>)
    requires A == multiset(a[..]) //pre'
    ensures Sorted(a[..])
    ensures multiset(a[..]) == multiset(old(a[..])) // == A. the same post condition as inserstion sort.
    modifies a
    {
        //introduce local variable + strengthen postcondition
        var i; //can be written as ghost var i, since we're just sending i's value to the lemma and not using it
        //the guard will not be satisfied and inv will
        i:= InsertionSort2(a,A);
        L2(a,i,A); //strengthen postcondition : the postcondition + i => InsertionSort1 postcondition
    }
method InsertionSort2(a:array<int>, ghost A: multiset<int>) returns (i: nat)
    requires A == multiset(a[..])
    ensures Inv1(a[..],i,A) && !Guard1(a,i,A) // the L2 lemma says it's okay.
    modifies a
    {
        i:=0; //skipping the laws of refinement
        while Guard1(a,i,A)
            invariant Inv1(a[..],i,A)
            decreases a.Length - i
            {
                Insert(a,i,A);
                i:=i+1;

            }
    }


//for example, when i=2 and a=[3,8,5,-1] we wish to insert the 5 into its sorted location in the prefix
//getting [3,5,8,-1], s.t we have [..i+1] sorted
method {:verify false} Insert(a:array<int>, i:nat, ghost A: multiset<int>)
    requires Inv1(a[..],i,A) && Guard1(a,i,A) //prefix in length i is sorted, and then i+1 then is sorted
    ensures Inv1(a[..], i+1,A) // for the incrementing of i.
    modifies a
    {
        // local variable + strengthen
        var j;
        j := Insert1(a,i,A);
        LemmaInsert(a,i,j,A);
    }

predicate Inv2(q: seq<int>, i:nat, j:nat, A: multiset<int>)
{
    j <= i < |q| && SortedExceptAt(q,j) && (forall k :: j < k <= i ==> q[j] < q[k]) &&
    multiset(q) == A
}
predicate method Guard2(a:array<int>, i:nat,j:nat, ghost A: multiset<int>)
    requires Inv2(a[..],i+1,j,A)
    reads a 
{
    exists k :: 0 <= k < j && a[k] > a[j]
}


lemma LemmaInsert(a:array<int>, i:nat, j:nat, A: multiset<int>)

    requires Inv2(a[..],i+1,j,A) && !Guard2(a,i,j,A) 
    ensures Inv1(a[..], i+1,A) 

method  Insert1(a:array<int>, i:nat, ghost A: multiset<int>) returns (j:nat)
    requires Inv1(a[..],i,A) && Guard1(a,i,A) 
    ensures Inv2(a[..], i+1,j,A)  && !Guard2(a,i,j,A)
    modifies a
    {
        LemmaInitJ(a,i,A);
        j := i;
        while Guard2(a,i,j,A)
            invariant Inv2(a[..],i+1,j,A)
            decreases j
            {
                Insert2(a,i,j,A);
                j := j-1;
            }
    }
lemma {:verify false} LemmaInitJ(a:array<int>, i:nat, A: multiset<int>)
    requires Inv1(a[..],i,A) && Guard1(a,i,A) 
    ensures Inv2(a[..], i+1,i,A)

method  Insert2(a:array<int>, i:nat, j:nat, ghost A: multiset<int>)
    requires Inv2(a[..],i,j,A) && Guard2(a,i,j,A) 
    ensures Inv2(a[..], i+1,j-1,A)  // && 0 <= j-1 < j
    modifies a
    {
        a[j-1],a[j] := a[j],a[j-1]
    }


/**
We have began with i <= |q| && Sorted(q[..i]) in Inv1, but there was a problem for Dfny to prove ensures multiset(a[..]) == A in L2
So we're adding it.
 */
predicate Inv1(q: seq<int>, i:nat, A: multiset<int>)
{

    i <= |q| && Sorted(q[..i]) && multiset(q) == A
}
predicate method Guard1(a:array<int>, i:nat, ghost A: multiset<int>)
    requires Inv1(a[..],i,A)
    reads a //needs permition to read the array in the heap while proving the program.
        // regular methods don't require this. predicate and function need to add "reads a" if accessing its values
{
    i != a.Length //can be written as i <a.Length. will help us w/ the negation of the guard.
}
/**
All lemmas's parameters are ghost!
we need to think about the main loop in the strength post condition.
 */
lemma L2(a:array<int>, i:nat, A: multiset<int>)
    requires Inv1(a[..],i,A) && !Guard1(a,i,A)
    ensures Sorted(a[..])
    ensures multiset(a[..]) == A


method Main() {
    var a: array<int> := new int[4];
    a[0],a[1],a[2],a[3] := 3,8,5,-1;
    print a[..];
    ghost var q := a[..]; //ghost variables allows in specification contexts (in asserts and such). they are not real variables (not taking place in memory)
    InsertionSort(a);
    assert Sorted(a[..]);
    assert multiset(a[..]) == multiset(q); // this is why we needed the ghost - instead of old(a) which is undefined in current context. 
}