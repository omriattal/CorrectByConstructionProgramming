predicate CommonDivisor(a: nat, b: nat, c: nat)
{
	c > 0 && a%c == b%c == 0
}

predicate GreatestCommonDivisor(a: nat, b: nat, c: nat)
{
	CommonDivisor(a, b, c) &&
	forall d: nat :: CommonDivisor(a, b, d) ==> d <= c
}

method {: verify false} ComputeGCD'(a: nat, b: nat) returns (i: nat)//verify false*******************
{
	if a<=b
	{
		i := a;
	}
	else
	{
		i := b;
	}
	while !(i > 0 && a%i == b%i == 0) //!CommonDivisor(a, b, i)
		invariant Inv(a, b, i)
		decreases i
	{
		i := i-1;
	}
}

method ComputeGCD(a: nat, b: nat) returns (i: nat)
	requires a > 0 && b > 0 //pre
	ensures GreatestCommonDivisor(a, b, i) //post
{
	// sequential composition + strengthen postcondition
	i := init(a,b);
	i := ComputeGCD2(a, b, i);
	LemmaStrengthenPostcondition(a, b, i);
}

lemma LemmaStrengthenPostcondition(a: nat, b: nat, i: nat)
	requires Inv(a, b, i) && Guard(a, b, i) //post'
	ensures GreatestCommonDivisor(a, b, i) //post
{}

predicate Inv(a: nat, b: nat, i: nat)
{
	i>0 && ( forall d: nat :: i<d ==> !CommonDivisor(a, b, d) )
}

predicate method Guard (a: nat, b: nat, i: nat)
{
	//CommonDivisor(a, b, i) - we could not use this predicate,
	//because it is only  a predicate and not a predicate method.
	//since the game do not allow us to change it, we left it this way...
	i > 0 && a%i == b%i == 0 
}

predicate method Guard2(a: nat, b: nat)
{
	a <= b
}
method init(a: nat, b: nat) returns (i: nat)
	requires a > 0 && b > 0 //pre
	ensures Inv(a, b, i)//mid
{
	// alternation
	if Guard2(a, b)
	{
		i := equalA(a, b);
	}
	else
	{
		i := equalB(a, b);
	}
}

method equalA(a: nat, b: nat) returns (i: nat)
	requires a > 0 && b > 0 && Guard2(a, b)
	ensures Inv(a, b, i)
{
	// assignment
	LemmaEqA(a, b, i);
	i := a;
}

lemma LemmaEqA(a: nat, b: nat, i: nat)
	requires a > 0 && b > 0 && Guard2(a, b)
	ensures Inv(a, b, a)
{}

method equalB(a: nat, b: nat) returns (i: nat)
	requires a > 0 && b > 0 && !Guard2(a, b)
	ensures Inv(a, b, i)
{	
	// assignment
	LemmaEqB(a, b, i);
	i := b;
}

lemma LemmaEqB(a: nat, b: nat, i: nat)
	requires a > 0 && b > 0 && !Guard2(a, b)
	ensures Inv(a, b, b)
{}

method ComputeGCD2(a: nat, b: nat, i0: nat) returns (i: nat)
	requires Inv(a, b, i0)//mid
	ensures Inv(a, b, i) && Guard(a, b, i) //post'
{
	i := i0;
	// iteration
	while !Guard(a, b, i)
		invariant Inv(a, b, i)
		decreases i
	{
		i := updateI(a, b, i);
	}
}

method updateI(a: nat, b:nat, i0: nat) returns (i: nat)
	requires Inv(a, b, i0) && !Guard(a, b, i0) 
	ensures Inv(a, b, i) && 0<=i<i0
{
	i := i0;
	// assignment
	LemmaUpdateI(a, b, i);
	i := i-1;
}

lemma LemmaUpdateI(a: nat, b: nat, i: nat)
	requires Inv(a, b, i) && !Guard(a, b, i) 
	ensures Inv(a, b, i-1) && 0<=i-1<i
{
	/* We may think on a situation in which i=0, and then 0<=-1<0 equal false, BUT it will never happen!
	Because i initialized with b>0, and since i=i-1 in each iteration, the minimun value i can get is 1.
	The reason for that is: for all tow natural numbers x,y : CommonDivisor(x,y,1) is true.
	It mean that our loop guard will equal false and we won't get to this update.
	Dafny failed to get it - we solved it by making Inv(a, b, i) stronger and ask for i>0. */ 
} 

method Main() {
	var x := ComputeGCD(8, 12);
	assert x == 4 by {
		assert CommonDivisor(8, 12, 4);
		assert forall x :: x > 4 ==> !CommonDivisor(8, 12, x);
	}
	print "GCD(8,12)=";
	print x;
	x := ComputeGCD(15, 6);
	assert x == 3 by {
		assert CommonDivisor(15, 6, 3);
		assert forall x :: x > 3 ==> !CommonDivisor(15, 6, x);
	}
	print "\nGCD(15,6)=";
	print x;
	x := ComputeGCD(10, 30);
	assert x == 10 by {
		assert CommonDivisor(10, 30, 10);
		assert forall x :: x > 10 ==> !CommonDivisor(10, 30, x);
	}
	print "\nGCD(10,30)=";
	print x;
	x := ComputeGCD(30, 10);
	assert x == 10 by {
		assert CommonDivisor(30, 10, 10);
		assert forall x :: x > 10 ==> !CommonDivisor(30, 10, x);
	}
	print "\nGCD(30,10)=";
	print x;
	x := ComputeGCD(100, 101);
	assert x == 1;
	print "\nGCD(100,101)=";
	print x;
}
