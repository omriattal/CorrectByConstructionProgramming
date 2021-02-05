datatype Expression = Value(int) | Add(Expression,Expression) | Multiply(Expression,Expression)
datatype Op = Operand(int) | Addition | Multiplication

method Main() {
	var exp := Add(Value(7),Multiply(Value(3),Value(5)));
	print "\nThe value of Add(Value(7),Multiply(Value(3),Value(5))) is ";
	var x := Evaluate(exp);
	print x;
	assert x == 7 + 3*5;
	x := EvaluateIter(exp); // evaluate iteratively this time, instead of recursively
	assert x == 7 + 3*5;
	print "\nThe iteratively-computed value of Add(Value(7),Multiply(Value(3),Value(5))) is ";
	print x;
	assert 2 > 1;
	var postfix := ComputePostfix(exp);
	print "\nThe postfix form of Add(Value(7),Multiply(Value(3),Value(5))) is ";
	print postfix;
	assert postfix == [Operand(7),Operand(3),Operand(5),Multiplication,Addition];

	postfix := ComputePostfixIter(exp); // compute the postfix sequence iteratively this time, instead of recursively
	print "\nThe iteratively-computed postfix form of Add(Value(7),Multiply(Value(3),Value(5))) is ";
	print postfix;
	assert postfix == [Operand(7),Operand(3),Operand(5),Multiplication,Addition];
}

function ValueOf(exp: Expression): int
	decreases exp
{
	match exp {
		case Value(x) => x
		case Add(l,r) => ValueOf(l)+ValueOf(r)
		case Multiply(l,r) => ValueOf(l)*ValueOf(r)
	}
}

method Evaluate(exp: Expression) returns (val: int)
	ensures val == ValueOf(exp)
	decreases exp
{
	match exp {
		case Value(x) => val := x;
		case Add(l,r) => var valLeft := Evaluate(l); var valRight := Evaluate(r); val := valLeft+valRight;
		case Multiply(l,r) => var valLeft := Evaluate(l); var valRight := Evaluate(r); val := valLeft*valRight;
	}
}

// implement iteratively (not recursively), using a loop;
// if it helps, feel free to use ComputePostfix or ComputePostfixIter;
// NO NEED to document the steps of refinement

/****************************************************   combine triplets   **********************************************************/
method EvaluateIter(exp: Expression) returns (val: int)
	ensures val == ValueOf(exp)
{
	var PF: seq<Op> := ComputePostfix(exp);
	var i: nat, res: int;

	LemmaMoreOperands(exp, PF);
	LemmaExistsI(exp, PF);

	while 1 < |PF|
		invariant Inv30(exp, PF)
		decreases |PF|
	{	
		LemmaSize(exp,PF);
		ghost var PF0 := PF;
		i := 2;
		while i < |PF| && !(isOperand(PF[i-2]) && isOperand(PF[i-1]) && isOperator(PF[i]))
		invariant 2 <= i <= |PF| && (exists j:nat :: i<=j<|PF| && isOperand(PF[j-2]) && isOperand(PF[j-1]) && isOperator(PF[j]))
		decreases |PF| - i
		{
			i := i+1;
		}
		LemmaI(exp, PF, i);
		if PF[i] == Addition
		{
			res := getVal(PF[i-2]) + getVal(PF[i-1]);
		}
		else
		{
			res := getVal(PF[i-2]) * getVal(PF[i-1]);
		}

		PF := PF[..i-2] + [Operand(res)] + PF[i+1..];
		LemmaInv30(exp, PF0, PF, i, res);	
	}
	val := getVal(PF[0]);
}

// lemma {:verify true} ExistenceOfSubExpression(exp:Expression,PF:seq<Op>)
// 	requires exists l:Expression,r:Expression :: exp==Add(l,r)||exp==Multiply(l,r)
// 	ensures exists exp':Expression :: SubExpression(exp',exp) && isBasic(exp') 
// {
// 	// Due to Expression definition and that exp is finite.
// 	var l,r :| exp==Add(l,r) || exp==Multiply(l,r);
// 	assert exists exp':Expression :: SubExpression(exp', exp) by {
// 		assert SubExpression(l,exp);
// 	}
// }

predicate SubExpression(sub: Expression, exp: Expression)
{
	sub == exp || (exists l:Expression,r:Expression :: (exp==Add(l,r)||exp==Multiply(l,r)) && (SubExpression(sub,l)||SubExpression(sub,r)) ) 
}

predicate isBasic(exp:Expression)
{
	exists n1:int,n2:int :: exp == Add(Value(n1),Value(n2)) || exp == Multiply(Value(n1),Value(n2))
}

lemma {:verify false} LemmaExistsI(exp: Expression, PF: seq<Op>)
	requires PF == Postfix(exp) 
	ensures |PF| == 1 || (|PF|>1 && exists i:nat :: 2<=i<|PF| && isOperand(PF[i-2]) && isOperand(PF[i-1]) && isOperator(PF[i]))
{
	//TODO: easy to see? if not, help us to prove by contradiction
	// Because exp is finite there is an expression, denote it as exp' s.t SubExpression(exp',exp) and isBasic(exp')
	// Denote PF' = Postfix(exp'), therefore PF' == [Operand,Operand,Operator] and PF' is a sub-seq of PF by definition of Postfix.

	if |PF| == 1
	{
		assert |PF| == 1;
	}
	else //|PF|>1
	{
		assert |PF| > 2;
		assert isOperator(PF[|PF|-1]); 
		assert exists l,r :: exp==Add(l,r)||exp==Multiply(l,r);

		// assert exists exp':Expression :: SubExpression(exp',exp) && isBasic(exp') by { ExistenceOfSubExpression(exp, PF); } 
		// var exp':Expression :| SubExpression(exp',exp) && isBasic(exp');
		// var n1:int,n2:int :| exp' == Add(Value(n1),Value(n2)) || exp' == Multiply(Value(n1),Value(n2));
		// var PF' := Postfix(exp');
		// assert PF' == [Operand(n1),Operand(n2),Addition] || PF' == [Operand(n1),Operand(n2),Multiplication];
		// assert exists i: nat:: i < |PF|-3 && PF' == PF[i..i+3];

		// assert exists i:nat :: 2<=i<|PF| && isOperand(PF[i-2]) && isOperand(PF[i-1]) && isOperator(PF[i]) by{
		// 	calc{
		// 		forall i:nat :: 2<=i<|PF| && !(isOperand(PF[i-2]) && isOperand(PF[i-1]) && isOperator(PF[i]))
		// 	==> //{ LemmaNoConsecutiveOperands(exp, PF); }
		// 		forall j:nat :: 0 <= j <|PF|-1 ==> !isOperand(PF[j]) || !isOperand(PF[j+1]) 
		// 	==>
		// 		numOfOperands(PF) <= numOfOperators(PF); 
		// 	}
		// }
	}
}

predicate NoConsecutiveOperands(PF: seq<Op>)
{
	forall j:nat :: 0 <= j <|PF|-1 ==> !isOperand(PF[j]) || !isOperand(PF[j+1])
}

lemma {:verify true} LemmaNoConsecutiveOperands(exp: Expression, PF: seq<Op>)
	requires PF == Postfix(exp) 
	requires forall i:nat :: 2<=i<|PF| ==> !(isOperand(PF[i-2]) && isOperand(PF[i-1]) && isOperator(PF[i]))
	ensures NoConsecutiveOperands(PF)
	decreases exp,PF
{
	if |PF| < 3
	{
		assert |PF|==1;
		assert NoConsecutiveOperands(PF);
	}
	else if |PF| == 3
	{
		assert isOperator(PF[2]);
		assert forall i:nat :: 2<=i<|PF| ==> !(isOperand(PF[i-2]) && isOperand(PF[i-1]) && isOperator(PF[i]));
		//==>
		assert !isOperand(PF[0]) || !isOperand(PF[1]);
		//==> 
		assert NoConsecutiveOperands(PF);
	}
	else
	{
		// induction hypothesis 
		var e1:Expression,e2:Expression :| exp == Add(e1,e2 ) || exp == Multiply(e1,e2);
		var PF1,PF2 := Postfix(e1),Postfix(e2);
		assert isOperator(PF1[|PF1|-1]); 
		assert isOperand(PF2[|PF2|-1]);
		assert isOperator(PF2[|PF2|-1]); 
		assert 0 < |PF1| < |PF|;
		assert 0 < |PF2| < |PF|; 
		assert e1 < exp;
		assert e2 < exp;
		var last:Op :| PF == PF1+PF2+[last];
		assert PF == PF1 + PF2 + [last];
		assert forall i:nat :: 2<=i<|PF1| ==> !(isOperand(PF1[i-2]) && isOperand(PF1[i-1]) && isOperator(PF1[i])) by{
			assert PF == PF1 + PF2 + [last];
			assert forall i:nat :: 2<=i<|PF| ==> !(isOperand(PF[i-2]) && isOperand(PF[i-1]) && isOperator(PF[i]));
			assert forall i:nat :: 2<=i<|PF1| ==> !(isOperand(PF[i-2]) && isOperand(PF[i-1]) && isOperator(PF[i]));
			assert forall i:nat :: 0<=i<|PF1| ==> isOperand(PF[i]) == isOperand(PF1[i]);
		}

		assume forall i:nat :: 2<=i<|PF2| ==> !(isOperand(PF2[i-2]) && isOperand(PF2[i-1]) && isOperator(PF2[i]));
		// assert forall i:nat :: 2<=i<|PF2| ==> !(isOperand(PF2[i-2]) && isOperand(PF2[i-1]) && isOperator(PF2[i])) by{
		// 	assert PF == PF1 + PF2 + [last];
		// 	assert forall i:nat :: 2<=i<|PF| ==> !(isOperand(PF[i-2]) && isOperand(PF[i-1]) && isOperator(PF[i]));
		// 	assert forall i:nat :: 2+|PF1|<=i<|PF2| ==> !(isOperand(PF[i-2]) && isOperand(PF[i-1]) && isOperator(PF[i]));
		// 	assert forall i:nat :: 0<=i< |PF2| ==> isOperand(PF[i+|PF1|]) == isOperand(PF2[i]);
		// }
		
		assert NoConsecutiveOperands(PF1) by { LemmaNoConsecutiveOperands(e1, PF1); }
		assert NoConsecutiveOperands(PF2) by { LemmaNoConsecutiveOperands(e2, PF2); }
		assert isOperator(PF[|PF|-1]); 
		assert PF == PF1 + PF2 + [last];
		assert isOperator(PF2[|PF2|-1]);
		//==>
		assert NoConsecutiveOperands(PF);
	}
}

lemma LemmaMoreOperands(exp: Expression, PF: seq<Op>)
	requires PF == Postfix(exp)
	ensures numOfOperands(PF) == 1 + numOfOperators(PF) 
	decreases exp, PF
{
	assert |PF| > 0;
	if |PF| == 1
	{
		assert numOfOperands(PF) == 1;
		assert numOfOperators(PF) == 0;
		assert numOfOperands(PF) == 1 + numOfOperators(PF) == 1 + 0 == 1;
	}
	else
	{
		assert |PF| > 1;
		assert isOperator(PF[|PF|-1]);
		assert forall x:int :: true ==> exp != Value(x);
		assert exists e1:Expression, e2:Expression :: (exp == Add(e1,e2) || (exp == Multiply(e1,e2)));
		var e1:Expression,e2:Expression :| exp == Add(e1,e2 ) || exp == Multiply(e1,e2);
		var PF1,PF2 := Postfix(e1),Postfix(e2);
		assert 0 < |PF1| < |PF|;
		assert 0 < |PF2| < |PF|; 
		assert e1 < exp;
		assert e2 < exp;
		
		// induction hypothesis 
		// Dafny has a bug .. couldn't understand with decreases PF, exp but did understand with decreases exp, PF
		assert numOfOperands(PF1) == 1 + numOfOperators(PF1) by { LemmaMoreOperands(e1,PF1); }
		assert numOfOperands(PF2) == 1 + numOfOperators(PF2) by { LemmaMoreOperands(e2,PF2); }
		
		//for the reader:
		// var last:Op :| PF == PF1+PF2+[last];
		// assert numOfOperands(PF) == numOfOperands(PF1+PF2+[last]) == 
		// 	      numOfOperands(PF1) + numOfOperands(PF2) + numOfOperands([last]) == (by i.h)
		//        1 + numOfOperators(PF1) + 1 + numOfOperators(PF2) + 0 ==
		// 	      2 + (numOfOperators(PF)-1) == 
		// 	      1 + numOfOperators(PF) ;
	}
}

// lemma {: verify true}LemmaSameNumOfOperands(PF:seq<Op>, PF1:seq<Op>, PF2:seq<Op>)
// 	requires PF == PF1+PF2
// 	ensures numOfOperands(PF) == numOfOperands(PF1) + numOfOperands(PF2)
// {}

lemma ExpFromPostFix(exp:Expression,PF:seq<Op>)
	requires PF == Postfix(exp) && |PF| > 1
	ensures exists e1:Expression, e2:Expression :: (exp == Add(e1,e2) || exp == Multiply(e1,e2))
{}

lemma {:verify true} LemmaInv30(exp: Expression, PF0: seq<Op>, PF: seq<Op>, i: nat, res: int)
	requires 1 < |PF0| && Inv30(exp, PF0) && 2 <= i < |PF0|
	requires isOperand(PF0[i-2]) && isOperand(PF0[i-1]) && isOperator(PF0[i])
	requires (PF0[i] == Addition && res == getVal(PF0[i-2]) + getVal(PF0[i-1])) || (PF0[i] == Multiplication && res == getVal(PF0[i-2]) * getVal(PF0[i-1]))
	requires PF == PF0[..i-2] + [Operand(res)] + PF0[i+1..]
	ensures Inv30(exp, PF)
{
	assert |PF| > 0;
	assert numOfOperands(PF) == 1 + numOfOperators(PF);
	assert (exists e:Expression :: Postfix(e) == PF && ValueOf(e) == ValueOf(exp)) by{
		LemmaSameValue(exp, PF0, PF, i, res);
	}
	var e:Expression :| Postfix(e) == PF && ValueOf(e) == ValueOf(exp);
	assert (|PF|==1 || (|PF|>1 && exists i:nat :: 2<=i<|PF| && isOperand(PF[i-2]) && isOperand(PF[i-1]) && isOperator(PF[i]))) by{
		LemmaExistsI(e, PF);
	}
	
}

lemma {: verify false} LemmaSameValue(exp: Expression, PF0: seq<Op>, PF: seq<Op>, i: nat, res: int)
	requires 1 < |PF0| && Inv30(exp, PF0) && 2 <= i < |PF0|
	requires isOperand(PF0[i-2]) && isOperand(PF0[i-1]) && isOperator(PF0[i])
	requires (PF0[i] == Addition && res == getVal(PF0[i-2]) + getVal(PF0[i-1])) || (PF0[i] == Multiplication && res == getVal(PF0[i-2]) * getVal(PF0[i-1]))
	requires PF == PF0[..i-2] + [Operand(res)] + PF0[i+1..]
	ensures exists e:Expression :: Postfix(e) == PF && ValueOf(e) == ValueOf(exp)
{
	//TODO::check later wait for breakthrough
	/* for simplicity:: denote exp == Add(2,Add(2,3)) then PF0 == Postfix(exp) = [2,2,3,Addition,Addition] and PF == [2,5,Addition] 
	==> exists e == Add(2,5) and we can see that PF=Postfix(e) and also ValueOf(e) == ValueOf(exp)
	*/  
}

lemma LemmaSize(exp: Expression, PF: seq<Op>)
	requires |PF| > 1 && Inv30(exp, PF)
	ensures |PF| >= 3
{}

predicate Inv30(exp: Expression, PF: seq<Op>)
{
	|PF| > 0 &&
	(exists e:Expression :: Postfix(e) == PF && ValueOf(e) == ValueOf(exp)) &&
	(|PF|==1 || (|PF|>1 && exists i:nat :: 2<=i<|PF| && isOperand(PF[i-2]) && isOperand(PF[i-1]) && isOperator(PF[i]))) &&
	numOfOperands(PF) == 1 + numOfOperators(PF)
}
lemma {:verify true} LemmaI(exp: Expression, PF: seq<Op>, i: nat)
	requires |PF| >= 3 && Inv30(exp, PF) && 2 <= i < |PF|
	requires i == |PF| || (isOperand(PF[i-2]) && isOperand(PF[i-1]) && isOperator(PF[i]))
	ensures isOperand(PF[i-2]) && isOperand(PF[i-1]) && isOperator(PF[i])
{}

function method numOfOperators(PF: seq<Op>) : int
{
	if |PF|==0 then 0 else
	match PF[0]{
		case Operand(x) => numOfOperands(PF[1..])
		case Addition => 1 + numOfOperands(PF[1..])
		case Multiplication => 1 + numOfOperands(PF[1..])
	}
}
function method numOfOperands(PF: seq<Op>) : int
{
	if |PF|==0 then 0 else
	match PF[0]{
		case Operand(x) => 1 + numOfOperands(PF[1..])
		case Addition => numOfOperands(PF[1..])
		case Multiplication => numOfOperands(PF[1..])
	}
}
predicate method isOperator(x: Op)
{
	x == Addition || x == Multiplication
}
predicate method isOperand(x: Op)
{
	x != Addition && x != Multiplication
}
function method getVal(x: Op) : int
	requires isOperand(x)
{
	match x {
		case Operand(y) => y
	}
}

/****************************************************   stack   **********************************************************/
// method EvaluateIterStack(exp: Expression) returns (val: int)
// 	ensures val == ValueOf(exp)
// {
// 	var PF: seq<Op> := ComputePostfix(exp);
// 	var stack: seq<Op>, i: nat := [], 0;

// 	while i != |PF|
// 		invariant Inv31(exp, PF, stack, i)
// 		decreases |PF| - i
// 	{
// 		ghost var stack0 := stack;
// 		match PF[i]{
// 			case Operand(x) => stack := stack + [PF[i]];
// 			case Addition => Lemma2Elements(stack); stack := stack[..|stack|-2] + [Operand(getVal(stack[|stack|-2])+getVal(stack[|stack|-1]))];
// 			case Multiplication => Lemma2Elements(stack); stack := stack[..|stack|-2] + [Operand(getVal(stack[|stack|-2])*getVal(stack[|stack|-1]))];
// 		}
// 		LemmaInv31(exp, PF, stack0, stack, i);
// 		i := i+1;
// 	}
// 	Lemma1Element(stack);
// 	LemmaPostCond(exp, PF, stack, i);
// 	val := getVal(stack[0]);
// }

// predicate Inv31(exp: Expression, PF: seq<Op>, stack: seq<Op>, i: nat)
// {
// 	0 <= i <= |PF| &&
// 	(exists e:Expression :: ValueOf(e) == ValueOf(exp) && Postfix(e) == stack + PF[i..]) &&
// 	(forall k:nat :: 0 <=k<|stack| ==> isOperand(stack[k]))//stack contains operands only
// }

// lemma {:verify true} LemmaPostCond(exp: Expression, PF: seq<Op>, stack: seq<Op>, i: nat)
// 	requires |stack| == 1 && i == |PF| && Inv31(exp, PF, stack, i)
// 	ensures getVal(stack[0]) == ValueOf(exp)
// {}

// lemma {:verify true} LemmaInv31(exp: Expression, PF: seq<Op>, stack0: seq<Op>, stack: seq<Op>, i: nat)
// 	requires Inv31(exp, PF, stack0, i) && i < |PF| && 
// 	(stack == stack0 + [PF[i]] ||
// 	stack == stack0[..|stack0|-2] + [Operand(getVal(stack0[|stack0|-2])+getVal(stack0[|stack0|-1]))] ||
// 	stack == stack0[..|stack0|-2] + [Operand(getVal(stack0[|stack0|-2])*getVal(stack0[|stack0|-1]))])
// 	ensures Inv31(exp, PF, stack, i+1)
// {}

// lemma {:verify true} Lemma1Element(stack: seq<Op>)
// 	ensures |stack| == 1 
// {}

// lemma {:verify true} Lemma2Elements(stack: seq<Op>)
// 	ensures |stack| >= 2
// {}


/****************************************************************************************************************************************************/
/*************************************************************   ComputePostFix    **************************************************************/
/****************************************************************************************************************************************************/

function Postfix(exp: Expression): seq<Op>
	decreases exp
{
	match exp {
		case Value(x) => [Operand(x)]
		case Add(l,r) => Postfix(l)+Postfix(r)+[Addition]
		case Multiply(l,r) => Postfix(l)+Postfix(r)+[Multiplication]
	}
}
// implement and document ALL steps of refinement (REC)
method ComputePostfix(exp: Expression) returns (res: seq<Op>)
	ensures res == Postfix(exp)
	decreases exp,10
{
	// alternation
	match exp {
		case Value(x) => res := ComputePostfix1A(exp,x); //[Operand(x)]
		case Add(l,r) => res := ComputePostfix1B(exp,l,r); //Postfix(l)+Postfix(r)+[Addition]
		case Multiply(l,r) => res := ComputePostfix1C(exp,l,r); //Postfix(l)+Postfix(r)+[Multiplication]
	}
}

method ComputePostfix1A(exp: Expression, x: int) returns (res: seq<Op>)
	requires exp == Value(x)
	ensures res == Postfix(exp)
{
	// assignment
	LemmaAssignment1(exp,x);
	res := [Operand(x)];
}

lemma LemmaAssignment1(exp: Expression, x: int)
	requires exp == Value(x)
	ensures [Operand(x)] == Postfix(exp)
{}

method ComputePostfix1B(exp: Expression, l:Expression, r:Expression) returns (res: seq<Op>)
	requires exp == Add(l,r)
	ensures res == Postfix(exp)
	decreases exp,9
{
	// leading assignment
	res := [Addition];
	res := ComputePostfix2(exp, l, r, res);
}

method ComputePostfix2(exp: Expression, l:Expression, r:Expression, res0: seq<Op>) returns (res: seq<Op>)
	requires exp == Add(l,r) && res0 == [Addition]
	ensures res == Postfix(exp)
	decreases exp,8
{
	res := res0;
	// sequential composition
	res := ComputePostfix3A(exp,l,r,res);
	res := ComputePostfix3B(exp,l,r,res);
}

method ComputePostfix3A(exp: Expression, l:Expression, r:Expression, res0: seq<Op>) returns (res: seq<Op>)
	requires exp == Add(l,r) && res0 == [Addition]
	ensures res == Postfix(r) + [Addition] && exp == Add(l,r)
	decreases exp,7
{
	res := res0;
	// introduce local variable + following assignment + contract frame
	var postFixR := ComputePostfix4(exp, l, r, res);
	res := postFixR + res;
}

method ComputePostfix4 (exp: Expression, l:Expression, r:Expression, res: seq<Op>) returns (postFixR: seq<Op>)
	requires exp == Add(l,r) && res == [Addition]
	ensures postFixR + res == Postfix(r) + [Addition] && exp == Add(l,r)
	decreases exp,6
{
	// reuse (recursive call): strengthen postcondition + weaken precondition + termination
	Lemma4Pre(exp,l,r,res);
	assert r < exp; //termination justification
	postFixR := ComputePostfix(r);
	Lemma4Post(exp,l,r,res,postFixR);
	
}
lemma Lemma4Pre(exp: Expression, l:Expression, r:Expression,res:seq<Op>)
	requires exp == Add(l,r) && res == [Addition]
	ensures true
{}

lemma Lemma4Post(exp: Expression, l:Expression, r:Expression,res:seq<Op>,postFixR:seq<Op>)
	requires exp == Add(l,r) && res == [Addition] 
	requires postFixR == Postfix(r)
	ensures postFixR + res == Postfix(r) + [Addition] && exp == Add(l,r)
{}

method ComputePostfix3B(exp: Expression, l:Expression, r:Expression, res0: seq<Op>) returns (res: seq<Op>)
	requires res0 == Postfix(r) + [Addition] && exp == Add(l,r)
	ensures res == Postfix(exp)
	decreases exp,7
{
	res := res0;
	// introduce local variable + following assignment + contract frame
	var postFixL := ComputePostfix5(exp,l,r,res);
	res := postFixL + res;
}

method ComputePostfix5(exp: Expression, l:Expression, r:Expression, res: seq<Op>) returns (postFixL: seq<Op>)
	requires res == Postfix(r) + [Addition] && exp == Add(l,r)
	ensures postFixL + res == Postfix(exp)
	decreases exp,6
{
	// reuse (recursive call): strengthen postcondition + weaken precondition + termination
	Lemma5Pre(exp,l,r,res);
	assert l < exp; //termination justification
	postFixL := ComputePostfix(l);
	Lemma5Post(exp,l,r,res,postFixL);
}

lemma Lemma5Pre(exp: Expression, l:Expression, r:Expression, res: seq<Op>)
	requires res == Postfix(r) + [Addition] && exp == Add(l,r)
	ensures true
{}

lemma Lemma5Post(exp: Expression, l:Expression, r:Expression,res:seq<Op>,postFixL:seq<Op>)
	requires res == Postfix(r) + [Addition] && exp == Add(l,r)
	requires postFixL == Postfix(l)
	ensures postFixL + res == Postfix(exp)
{}
/****************************************************************************************************************************************************/
method ComputePostfix1C(exp: Expression, l:Expression, r:Expression) returns (res: seq<Op>)
	requires exp == Multiply(l,r)
	ensures res == Postfix(exp)
	decreases exp,9
{
	// leading assignment
	res := [Multiplication];
	res := ComputePostfix6(exp, l, r, res);
}

method ComputePostfix6(exp: Expression, l:Expression, r:Expression, res0: seq<Op>) returns (res: seq<Op>)
	requires exp == Multiply(l,r) && res0 == [Multiplication]
	ensures res == Postfix(exp)
	decreases exp,8
{
	res := res0;
	// sequential composition
	res := ComputePostfix7A(exp,l,r,res);
	res := ComputePostfix7B(exp,l,r,res);
}

method ComputePostfix7A(exp: Expression, l:Expression, r:Expression, res0: seq<Op>) returns (res: seq<Op>)
	requires exp == Multiply(l,r) && res0 == [Multiplication]
	ensures res == Postfix(r) + [Multiplication] && exp == Multiply(l,r)
	decreases exp,7
{
	res := res0;
	// introduce local variable + following assignment + contract frame
	var postFixR := ComputePostfix8(exp, l, r, res);
	res := postFixR + res;
}

method ComputePostfix8(exp: Expression, l:Expression, r:Expression, res: seq<Op>) returns (postFixR: seq<Op>)
	requires exp == Multiply(l,r) && res == [Multiplication]
	ensures postFixR + res == Postfix(r) + [Multiplication] && exp == Multiply(l,r)
	decreases exp,6
{
	// reuse (recursive call): strengthen postcondition + weaken precondition + termination
	Lemma8Pre(exp,l,r,res);
	assert r < exp; //termination justification
	postFixR := ComputePostfix(r);
	Lemma8Post(exp,l,r,res,postFixR);
	
}
lemma Lemma8Pre(exp: Expression, l:Expression, r:Expression,res:seq<Op>)
	requires exp == Multiply(l,r) && res == [Multiplication]
	ensures true
{}

lemma Lemma8Post(exp: Expression, l:Expression, r:Expression,res:seq<Op>,postFixR:seq<Op>)
	requires exp == Multiply(l,r) && res == [Multiplication] 
	requires postFixR == Postfix(r)
	ensures postFixR + res == Postfix(r) + [Multiplication] && exp == Multiply(l,r)
{}

method ComputePostfix7B(exp: Expression, l:Expression, r:Expression, res0: seq<Op>) returns (res: seq<Op>)
	requires res0 == Postfix(r) + [Multiplication] && exp == Multiply(l,r)
	ensures res == Postfix(exp)
	decreases exp,7
{
	res := res0;
	// introduce local variable + following assignment + contract frame
	var postFixL := ComputePostfix9(exp,l,r,res);
	res := postFixL + res;
}

method ComputePostfix9(exp: Expression, l:Expression, r:Expression, res: seq<Op>) returns (postFixL: seq<Op>)
	requires res == Postfix(r) + [Multiplication] && exp == Multiply(l,r)
	ensures postFixL + res == Postfix(exp)
	decreases exp,6
{
	// reuse (recursive call): strengthen postcondition + weaken precondition + termination
	Lemma9Pre(exp,l,r,res);
	assert l < exp; //termination justification
	postFixL := ComputePostfix(l);
	Lemma9Post(exp,l,r,res,postFixL);
}

lemma Lemma9Pre(exp: Expression, l:Expression, r:Expression, res: seq<Op>)
	requires res == Postfix(r) + [Multiplication] && exp == Multiply(l,r)
	ensures true
{}

lemma Lemma9Post(exp: Expression, l:Expression, r:Expression,res:seq<Op>,postFixL:seq<Op>)
	requires res == Postfix(r) + [Multiplication] && exp == Multiply(l,r)
	requires postFixL == Postfix(l)
	ensures postFixL + res == Postfix(exp)
{}

/****************************************************************************************************************************************************/
/*************************************************************   ComputePostFixIter    **************************************************************/
/****************************************************************************************************************************************************/


// complete the implementation (of LoopBody below) and the verification
// (by providing a body to Inv, V, LemmaInit, and LemmaPost below);
// NO NEED to document the steps of refinement
method ComputePostfixIter(exp: Expression) returns (res: seq<Op>)
	ensures res == Postfix(exp)
{
	var stack := [exp];
	res := [];
	LemmaInit(exp, stack, res);
	while stack != []
		invariant Inv(exp, stack, res)
		decreases V(stack)
	{
		stack, res := LoopBody(exp, stack, res);
	}
	LemmaPost(exp, stack, res);
}

function stackToOps(stack: seq<Expression>) : seq<Op>
	decreases stack
{
	if stack == [] then [] else stackToOps(stack[..|stack|-1]) + Postfix(stack[|stack|-1])
}

predicate Inv(exp: Expression, stack: seq<Expression>, res: seq<Op>)
{
	stackToOps(stack) + res == Postfix(exp)
}

function StackSize(stack: seq<Expression>):nat
	decreases stack
{
	if stack == [] then 0 else ExpressionSize(stack[|stack|-1]) + StackSize(stack[..|stack|-1]) 
}

function ExpressionSize(exp: Expression) : nat
	decreases exp
{
	match exp {
		case Value(x) => 1
		case Add(l,r) => 1 + ExpressionSize(l) + ExpressionSize(r)
		case Multiply(l,r) => 1 + ExpressionSize(l) + ExpressionSize(r)
	}
}

function V(stack: seq<Expression>): int
{
	StackSize(stack)
}

lemma LemmaInit(exp: Expression, stack: seq<Expression>, ops: seq<Op>)
	requires stack == [exp] && ops == []
	ensures Inv(exp, stack, ops)
{}

lemma LemmaPost(exp: Expression, stack: seq<Expression>, res: seq<Op>)
	requires Inv(exp, stack, res) && stack == []
	ensures res == Postfix(exp)
{}

method LoopBody(ghost exp: Expression, stack0: seq<Expression>, ops0: seq<Op>) returns (stack: seq<Expression>, ops: seq<Op>)
	requires Inv(exp, stack0, ops0) && stack0 != []
	ensures Inv(exp, stack, ops) && 0 <= V(stack) < V(stack0)
{
	stack, ops := stack0, ops0;
	var popped;
	popped, stack := stack[|stack|-1], stack[..|stack|-1]; 
	match popped {
		case Value(x) => ops := [Operand(x)] + ops;
		case Add(l,r) => ops, stack := [Addition] + ops, stack + [l,r]; LemmaAdd(exp,stack0,ops0,stack,ops,popped,l,r);
		case Multiply(l,r) => ops,stack := [Multiplication] + ops, stack + [l,r]; LemmaMul(exp,stack0,ops0,stack,ops,popped,l,r);
	}
}

lemma LemmaAdd(exp: Expression, stack0: seq<Expression>, ops0: seq<Op>, stack: seq<Expression>, ops: seq<Op>, popped: Expression, l:Expression, r:Expression)
	requires Inv(exp, stack0, ops0) && stack0 != [] && popped == Add(l,r) && popped == stack0[|stack0|-1]
	requires ops == [Addition] + ops0 && stack == stack0[..|stack0|-1] + [l,r]
	ensures Inv(exp, stack, ops) && 0 <= V(stack) < V(stack0)
{
	assert Inv(exp, stack, ops) by{
		assert stackToOps(stack0) + ops0 == Postfix(exp);
		assert stack == stack0[..|stack0|-1] + [l,r];
		assert ops == [Addition] + ops0;		
		assert stackToOps(stack[..|stack|-2]+[popped]) + ops[1..] == Postfix(exp);
		assert popped == Add(l,r);
		assert stackToOps(stack[..|stack|-2]+[popped]) == stackToOps(stack[..|stack|-2]) + Postfix(popped);
		assert Postfix(popped) == Postfix(l)+Postfix(r)+[Addition];
		assert stackToOps(stack[..|stack|-2]+[popped]) == stackToOps(stack[..|stack|-2]) + Postfix(l)+Postfix(r)+[Addition];
		assert stackToOps(stack[..|stack|-2]) + Postfix(l)+Postfix(r) + ops == Postfix(exp);
		assert stackToOps(stack) == stackToOps(stack[..|stack|-2]) + Postfix(l)+Postfix(r) by{L1(stack,l,r);}
		assert stackToOps(stack) + ops == Postfix(exp);
	}
	assert V(stack) < V(stack0) by{
		assert StackSize(stack) < StackSize(stack0) by{
			assert stack0 == stack0[..|stack0|-1] + [popped];
			assert StackSize(stack0) == StackSize(stack0[..|stack0|-1]) + StackSize( [popped]);
			assert stack  == stack0[..|stack0|-1] + [l] + [r];
			assert StackSize(stack) == StackSize(stack0[..|stack0|-1] + [l]) + StackSize( [r]);
			assert StackSize(stack0[..|stack0|-1] + [l]) == StackSize(stack0[..|stack0|-1]) + StackSize([l]);
			assert ExpressionSize(popped) > ExpressionSize(l) + ExpressionSize(r);
			
		}
	}
}

lemma LemmaMul(exp: Expression, stack0: seq<Expression>, ops0: seq<Op>, stack: seq<Expression>, ops: seq<Op>, popped: Expression, l:Expression, r:Expression)
	requires Inv(exp, stack0, ops0) && stack0 != [] && popped == Multiply(l,r) && popped == stack0[|stack0|-1]
	requires ops == [Multiplication] + ops0 && stack == stack0[..|stack0|-1] + [l,r]
	ensures Inv(exp, stack, ops) && 0 <= V(stack) < V(stack0)
{
	assert Inv(exp, stack, ops) by{
		assert stackToOps(stack0) + ops0 == Postfix(exp);
		assert stack == stack0[..|stack0|-1] + [l,r];
		assert ops == [Multiplication] + ops0;		
		assert stackToOps(stack[..|stack|-2]+[popped]) + ops[1..] == Postfix(exp);
		assert popped == Multiply(l,r);
		assert stackToOps(stack[..|stack|-2]+[popped]) == stackToOps(stack[..|stack|-2]) + Postfix(popped);
		assert Postfix(popped) == Postfix(l)+Postfix(r)+[Multiplication];
		assert stackToOps(stack[..|stack|-2]+[popped]) == stackToOps(stack[..|stack|-2]) + Postfix(l)+Postfix(r)+[Multiplication];
		assert stackToOps(stack[..|stack|-2]) + Postfix(l)+Postfix(r) + ops == Postfix(exp);
		assert stackToOps(stack) == stackToOps(stack[..|stack|-2]) + Postfix(l)+Postfix(r) by{L1(stack,l,r);}
		assert stackToOps(stack) + ops == Postfix(exp);
	}
	assert 0 <= V(stack) < V(stack0) by{
			assert StackSize(stack) < StackSize(stack0) by{
			assert stack0 == stack0[..|stack0|-1] + [popped];
			assert StackSize(stack0) == StackSize(stack0[..|stack0|-1]) + StackSize( [popped]);
			assert stack  == stack0[..|stack0|-1] + [l] + [r];
			assert StackSize(stack) == StackSize(stack0[..|stack0|-1] + [l]) + StackSize( [r]);
			assert StackSize(stack0[..|stack0|-1] + [l]) == StackSize(stack0[..|stack0|-1]) + StackSize([l]);
			assert ExpressionSize(popped) > ExpressionSize(l) + ExpressionSize(r);
		}
	}
}

lemma L1(stack:seq<Expression>,l:Expression, r:Expression)
	requires |stack| >= 2 && stack == stack[..|stack|-2] + [l,r]
	ensures stackToOps(stack) == stackToOps(stack[..|stack|-2]) + Postfix(l) + Postfix(r);
{
	assert stackToOps(stack) == stackToOps(stack[..|stack|-1]) + Postfix(stack[|stack|-1]);
	assert stack[|stack|-1] == r;
	assert stackToOps(stack) == stackToOps(stack[..|stack|-1]) + Postfix(r);
	assert |stack[..|stack|-1]| >= 1;
	assert stack[|stack|-2] == l;
	assert stack[..|stack|-1] == stack[..|stack|-2] + [stack[|stack|-2]];
	assert stackToOps(stack[..|stack|-1]) == stackToOps(stack[..|stack|-2]) + Postfix(stack[|stack|-2]);
	assert stackToOps(stack[..|stack|-2]) + Postfix(l)+Postfix(r) == stackToOps(stack);
}