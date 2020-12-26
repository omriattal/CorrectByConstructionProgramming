predicate Sorted(q: seq<int>)
{
    forall i,j :: 0<= i <= j < |q| ==> q[i] <= q[j]
}
predicate SortedExceptAt(q: seq<int>, k: nat)
    {
        forall i,j :: 0<=i<=j < |q| && i!=k && j!=k ==> q[i] <= q[j]
    }
method InsertionSort(a: array<int>)
    requires true // pre
    ensures forall i :: 0 <= i < a.Length -1  ==> a[i] <= a[i+1] 
    ensures multiset(a[..]) == multiset(old(a[..]))
    modifies a 
    {
      
        ghost var A :| A == multiset(a[..]);
        InsertionSort1(a,A);

    }
    predicate Inv1(q: seq<int>, i:nat, A: multiset<int>)
{

    i <= |q| && Sorted(q[..i]) && multiset(q) == A
}
predicate method Guard1(a:array<int>, i:nat, ghost A: multiset<int>)
    requires Inv1(a[..],i,A)
    reads a 
{
    i != a.Length 
}
       



lemma L2(a:array<int>, i:nat, A: multiset<int>)
    requires Inv1(a[..],i,A) && !Guard1(a,i,A)
    ensures Sorted(a[..])
    ensures multiset(a[..]) == A
method InsertionSort1(a:array<int>, ghost A: multiset<int>)
    requires A == multiset(a[..]) //pre'
    ensures Sorted(a[..])
    ensures multiset(a[..]) == multiset(old(a[..]))
    modifies a
    {
        var i; 
        i:= InsertionSort2(a,A);
        L2(a,i,A); 
    }
method InsertionSort2(a:array<int>, ghost A: multiset<int>) returns (i: nat)
    requires A == multiset(a[..])
    ensures Inv1(a[..],i,A) && !Guard1(a,i,A)
    modifies a
    {
        i:=0; 
        while Guard1(a,i,A)
            invariant Inv1(a[..],i,A)
            decreases a.Length - i
            {
                Insert(a,i,A);
                i:=i+1;

            }
    }

method {:verify false} Insert(a:array<int>, i:nat, ghost A: multiset<int>)
    requires Inv1(a[..],i,A) && Guard1(a,i,A) 
    ensures Inv1(a[..], i+1,A) 
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


predicate method Guard2' (a:array<int>, i:nat,j:nat, ghost A: multiset<int>)
    requires Inv2(a[..],i,j,A)
    reads a 
{
   j < 0 && a[j-1] > a[j] // this and the invariant implies the guard2.
}

lemma  LemamEquivalentGuards (a:array<int>, i:nat,j:nat, A: multiset<int>)
    ensures Guard2(a,i,j,A) <==> Guard2'(a,i,j,A) //can be == 

predicate method Guard2(a:array<int>, i:nat,j:nat, ghost A: multiset<int>)
    requires Inv2(a[..],i,j,A)
    reads a 
{
    exists k :: 0 <= k < j && a[k] > a[j]
}


lemma LemmaInsert(a:array<int>, i:nat, j:nat, A: multiset<int>)

    requires Inv2(a[..],i,j,A) && !Guard2(a,i,j,A) 
    ensures Inv1(a[..], i,A) 


/**
we had a major bug while trying to prove lemmainitJ, we discovered incorrect use of i+1, instead changed to i 
 */
method  Insert1(a:array<int>, i:nat, ghost A: multiset<int>) returns (j:nat)
    requires Inv1(a[..],i,A) && Guard1(a,i,A) 
    ensures Inv2(a[..], i,j,A)  && !Guard2(a,i,j,A) // we need that !guard2 ==> guard1!
    modifies a
    {
        LemmaInitJ(a,i,j,A);
        j := i;
        while Guard2' (a,i,j,A) // more efficient than guard2. we need that in the loop guard2' ==> guard!
            invariant Inv2(a[..],i,j,A)
            decreases j
            {
                LemamEquivalentGuards(a,i,j,A);
                Insert2(a,i,j,A);
                j := j-1;
            }
        LemamEquivalentGuards(a,i,j,A);
    }
lemma {:verify false} LemmaInitJ(a:array<int>, i:nat, j: nat, A: multiset<int>)
    requires Inv1(a[..],i,A) && Guard1(a,i,A) 
    ensures Inv2(a[..], i,i,A)
    {
        // var q := a[..]; //this is ghosted
        // assert i <= |q|; // pre1
        // assert Sorted(q[..i]); //pre2
        // assert multiset(q) == A; //pre3
        // assert i != a.Length; //pre4
        // //we need to prove
        // var i',j := i+1,i;
        // assert j <= i' < |q|; //post1
        // assert SortedExceptAt(q[..i'+1],j); //post2
        // assert forall k :: j < k <= i' ==> q[j] < q[k] by {
        //     assert forall k :: i < k <= i+1 ==> q[i] <q[k];
        // }
        // assert multiset(q) == A; //post4 from pre3
    }

method  Insert2(a:array<int>, i:nat, j:nat, ghost A: multiset<int>)
    requires Inv2(a[..],i,j,A) && Guard2(a,i,j,A) 
    ensures Inv2(a[..], i,j-1,A)  // && 0 <= j-1 < j
    modifies a
    {
        // assignment, so we need to prove it w/ a lemma
        LemmaSwap(a,i,j,A);
        a[j-1],a[j] := a[j],a[j-1];
    }

    /**
    There is a complication here since the substituiton here is not that easy.
    usually we substitute the leftside with the rightside to verify the postcond.
    a[..][] is a substitution inside the array.
    the postcondition of the lemma is with the substitution of the assignment.
     */
method  LemmaSwap(a:array<int>, i:nat, j:nat,  A: multiset<int>)
    requires Inv2(a[..],i,j,A) && Guard2(a,i,j,A) //with the guard, it's implied that j > 0
    ensures Inv2(a[..][j-1 := a[j]][j := a[j-1]], i,j-1,A)
    {
        var q := a[..]; 
        assert j <= i < |q|; //pre1
        assert SortedExceptAt(q[..i+1],j); //pre2
        assert forall k :: j < k <= i ==> q[i] < q[k]; //pre3
        assert multiset(q) == A; //pre4
        assert exists k :: 0<= k < j && a[k] > a[j]; //pre5
        //we need to show the following
        var q' := a[..][j-1 := a[j]][j := a[j-1]];
        var j' := j-1;
        // all the stuff below are with this substitution
        //post1
        assert j' <= i < |q'| by { //left conjuct from left of pre1
            assert |q| == |q'|; // right conjuct from right of pre1 and this
        }
        //post2
        assert SortedExceptAt(q'[..i+1],j') by {
            var q1 := q'[..i+1];
            var k := j';
            //this is the first time we meet ensures in assert forall. 
            // we stopped here.
            forall i1,j1 | 0 <= i1 <= j1 < |q1| && i1 != j-1 && j1 != j-1 ensures q1[i1] <= q1[j1] { //forall is a boolean expression
                if i1 == j1
                {
                    assert q1[i1] == q1[j1];
                }
                else
                {
                    assert i1 < j1;
                    if i1 == j
                    {
                        assert q1[i1] == q1[j] == q[j-1];
                        assert SortedExceptAt(q[..i+1],j);
                    }
                    else if i1 == j
                    {
                        assert q1[j1] == q1[j] == q[j-1];
                    }
                }
            }
        }
        //post3
        assert forall k :: j' < k <= i ==> q'[j'] < q'[k];
        assert multiset(q') == A;
    }



method Main() {
    var a: array<int> := new int[4];
    a[0],a[1],a[2],a[3] := 3,8,5,-1;
    print a[..];
    ghost var q := a[..]; //ghost variables allows in specification contexts (in asserts and such). they are not real variables (not taking place in memory)
    InsertionSort(a);
    assert Sorted(a[..]);
    assert multiset(a[..]) == multiset(q); // this is why we needed the ghost - instead of old(a) which is undefined in current context. 
}