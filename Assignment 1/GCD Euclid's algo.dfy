/*
gcd(a, b):
	r=a%b
	while(r!=0)         GUARD
		INV				gcd(a0,b0) == gcd(a,b) && a>=b
		DEC b			0<=b<b0, because b0 == a%b < b
	{
		a=b
		b=r
		r=a%b 
	}

	WHAT DO WE KNOW AT THIS POINT?
	1. gcd(a,b) == gcd(new_a, new_b) because the transitive relation
	2. new_a >= new_b
	3. r=0 && r= a_new % b_new ==> gcd(new_a,new_b) == Min{new_a,new_b} == new_b
	4. So gcd(a,b) == new_b so just make the assignment: c=new_b
	
	return b
	--------------------------------------------------------------
	def gcd(a,b)
	while b!=0
		a, b = b, a%b
	return a;
*/
predicate CommonDivisor(a: nat, b: nat, c: nat)
{
	c > 0 && a%c == b%c == 0
}

predicate GreatestCommonDivisor(a: nat, b: nat, c: nat)
{
	CommonDivisor(a, b, c) &&
	forall d: nat :: CommonDivisor(a, b, d) ==> d <= c
}

// method ComputeGCD(a: nat, b: nat) returns (i: nat)
// 	requires a > 0 && b > 0
// 	ensures GreatestCommonDivisor(a, b, i)
// {
	
// }

// method ComputeGCD1(a: nat, b: nat) returns (i: nat, x:nat, y:nat)
// 	requires a > 0 && b > 0
// 	ensures GreatestCommonDivisor(a, b, i)
// {
// 	// sequential composition + strengthen postcondition
// 	i, x, y := Init(a, b);
// 	i, x, y:= Loop(a, b, i, x, y);
//     LemmaStrengthenPostcondition(a, A, i, j);
// }

// method Init(a: nat, b: nat) returns (i: nat, x:nat, y:nat)
// 	requires a > 0 && b > 0
// {}

method ComputeGCD(a: nat, b: nat) returns (i: nat)
	requires a > 0 && b > 0
	ensures GreatestCommonDivisor(a, b, i)
{
	var x,y;
	x,y := a,b;
	while y!=0
		invariant Inv(a,b,x,y)
	{
		x,y := y,x%y;
	}
	i := x;
}

predicate Inv(a: nat, b: nat, x: nat, y: nat)
{
	forall j:nat :: CommonDivisor(a,b,j) <==> CommonDivisor(x,y,j) 
}
/**
Lemma:
for all j on the face of the earth, commonDivisor(a,b,i) <==> commonDivisor(x,y,i)
 */
 /**
 Alternative lemma:
 for all j GCD(a,b,j) <==> GCD(x,y,j)
  */
 /**
 Lemma
 for all k > 0 gcd(k,0) == k
  */
  /**
  assignment: i = gcd(x,y = 0) = x
   */

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
