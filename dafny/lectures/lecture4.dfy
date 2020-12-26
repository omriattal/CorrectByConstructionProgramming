method {:verify false} Sqrt(n:nat) returns (a:nat)
    ensures a*a <= n < (a+1)*(a+1)
    {
        var b : nat; //not specifying the nat made dafny mad since we did an assignment of nat to b. 
        // assert forall n: nat :: true ==> 0*0 <= n < n*n 
        // this is not correct, so the assignment a,b := 0,n does not satisfy the invariant of the loop (does not established it)
        assert forall n: nat :: true ==> 0*0 <= n < (n+1)*(n+1);
        a,b := 0,n+1;
        assert a*a <= n < b*b;
        while b!=a+1
            invariant a*a <= n < b*b
            decreases b*b - a*a // possible : b - a.
            {
                a,b := loopBody(n,a,b);
            }
        assert a*a <= n < b*b; // the invariant is correct after the loop
        assert b == a+1; // the negation of the loop guard
        assert a*a <= n < (a+1)*(a+1);
    }

method {:verify false} Sqrt'(n:nat) returns (a:nat)
    ensures a*a <= n < (a+1)*(a+1)
    {
        var b : nat;
        a,b := 0,n+1;
        while b!=a+1
            invariant a*a <= n < b*b
            decreases b*b - a*a 
            {
                var m := (a+b)/2;
                if m*m <= n
                {
                    a := m;
                }
                else
                {
                    b := m;
                }
                
            }
        assert a*a <= n < b*b; // the invariant is correct after the loop
        assert b == a+1; // the negation of the loop guard
        assert a*a <= n < (a+1)*(a+1);
    }


method {:verify false} loopBody (n:nat, a0:nat, b0:nat) returns (a:nat, b: nat)
    requires a0*a0 <= n < b0*b0 // the loop invariant
    requires b0 != a0 + 1 // the loop guard
    ensures a*a <= n < b*b //retuens a,b such that they preserve the loop invariant
    ensures 0 <= b*b - a*a < b0*b0 - a0*a0 //guarantee loop termination
    {
        a,b := a0, b0; //convention, since we can't change a0 and b0
        var m := (a+b)/2 ; //to avoid overflow could say a+(b-1)/2. here in dafny, our nats and ints are not bounded
        a,b := update(n,a,b,m); // dafny outputs no errors, update's precond, postconds match and we just need to implement update's body.
    } 


 predicate method Guard (n: nat,a: nat,b: nat,m: nat) // method for making it executable. just predicate is like a function
 {
     m*m <= n
 }
    
 method {:verify false} update (n:nat, a0:nat, b0:nat, m:nat) returns (a:nat, b: nat) 
    requires a0*a0 <= n < b0*b0 
    requires b0 != a0 + 1 
    requires a0 < m < b0
    ensures a*a <= n < b*b
    ensures 0 <= b*b - a*a < b0*b0 - a0*a0 
    {
        a,b :=  a0,b0;
        if Guard(n,a,b,m)
        {
            a := updateA(n,a,b,m);
        }
        else
        {
            b := updateB(m,a,b,m);
        }
    }

/**
This lemma is supposed to replace the complicated assert forall in updateA.
It is used here to help us prove the assignment, and for the reader of the code.
The body of the lemma is a proof.
note that the lemma should be right on its own (i.e not basing its correctes on past computations and remarks)
lemmas can be called like methods
 */
lemma {:verify false} proofOfUpdateA (n:nat, a:nat,b:nat,m:nat)
    requires a*a <= n < b*b 
    requires b != a + 1 
    requires a < m < b // can be also the exact value of m (the middle)
    requires Guard (n,a,b,m)
    ensures m*m <= n < b*b //substitution
    ensures 0 <= b*b - m*m < b*b - a*a
    {

        assert 0 <= a < m; //not mandatory here as oppose to the assert forall used in updateA
    }

 method {:verify false} updateA (n:nat, a0:nat, b:nat, m:nat) returns (a:nat) 
    requires a0*a0 <= n < b*b 
    requires b != a0 + 1 
    requires a0 < m < b // can be also the exact value of m (the middle)
    requires Guard (n,a0,b,m)
    ensures a*a <= n < b*b
    ensures 0 <= b*b - a*a < b*b - a0*a0
    {
        a := a0;
        // assert forall a : nat, n: nat, b: nat, m:nat, a0: nat  ::
        //   a == a0 && a0 * a0 <= n < b*b && b!= a0 + 1 && a0 < m < b && Guard(n,a0,b,m)
        //     ==> m*m <= n < b*b && 0 <= b*b - m*m < b*b - a0*a0 by
        //     {
        //         assert 0 <= a == a0 < m; // to convince dafny that  0 <= b*b - m*m < b*b - a0*a0 is true, since we know it because a0<m
        //     }        
        proofOfUpdateA(n,a,b,m) ; 
        a := m;
    }


lemma {:verify true} proofOfUpdateB (n:nat, a:nat,b:nat,m:nat)
    requires a*a <= n < b*b  //pre0
    requires b != a + 1      //pre1
    requires a < m < b       //pre2
    requires !Guard(n,a,b,m) //pre3: ! (m*m <= n)
    ensures a*a <= n < b*b   //post0,1
    ensures 0 <= m*m - a*a < b*b - a*a //post 2,3
    {
        //post0
        assert a*a <= n; // from left side of pre0
        //post1
        assert n < m*m; //from pre3
        //post2
        assert 0 <= m*m-a*a; //from post0 and post1 with transitivity
        assert m*m - a*a < b*b - a*a by { 
            assert m*m < b*b by {
                assert 0<= m < b;
                NatSquareMonotinicity(m,b);
            } //right side from pre2 and m,b are natural numbers        
        }
    }

lemma NatSquareMonotinicity (x:nat,y:nat)
    requires x < y
    ensures x*x < y*y
    {

    }
 method {:verify false} updateB (n:nat, a:nat, b0:nat, m:nat) returns (b:nat) 
    requires a*a <= n < b0*b0 
    requires b0 != a + 1 
    requires a < m < b0 
    requires !Guard(n,a,b0,m)
    ensures a*a <= n < b*b
    ensures 0 <= b*b - a*a < b0*b0 - a*a
    {
        b := b0;
        /**
        We saw here assume and not assert because we didn't succeed proving the assert
        //  */
        //  assert forall a : nat, n: nat, b0: nat, m:nat, a0: nat  ::
        //   b == b0 && a * a <= n < b0*b0 && b0!= a0 + 1 && a < m < b0 && Guard(n,a,b0,m)
        //     ==> a*a <= n < m*m && 0 <= m*m - a*a < b0*b0 - a*a by
        //     {
        //         assert 0<= m <  b0 == b;   
        //     }
        proofOfUpdateB(n,a,b,m);
        b := m;
    }