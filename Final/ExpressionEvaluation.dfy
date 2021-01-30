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

// function ValueOfOps(ops: seq<Op>, exp: Expression): int
// 	requires ops == Postfix(exp)
// {}

// TODO: implement iteratively (not recursively), using a loop;
// if it helps, feel free to use ComputePostfix or ComputePostfixIter;
// NO NEED to document the steps of refinement
// method {:verify true} EvaluateIter(exp: Expression) returns (val: int)
// 	ensures val == ValueOf(exp)
// {
// 	var stack: seq<int>, i: nat := [], 0;
// 	var expPostFix := ComputePostfixIter(exp);
// 	while i < |expPostFix|
// 		invariant Inv5(exp, stack, expPostFix, i)
// 		decreases |expPostFix| - i
// 	{
// 		match expPostFix[i]{
// 			case Operand(x)     => stack := stack + [x];
// 			case Addition       => Lemma2Elements(stack); stack := stack[..|stack|-2] + [ stack[|stack|-1] + stack[|stack|-2] ];
// 			case Multiplication => Lemma2Elements(stack); stack := stack[..|stack|-2] + [ stack[|stack|-1] * stack[|stack|-2] ];
// 		}
// 		i := i + 1;
// 	}
// 	Lemma1Element(stack);
// 	val := stack[0];
// }

// predicate Inv5(exp: Expression, stack: seq<int>, expPostFix: seq<Op>, i:nat)
// {
// 	0 <= i <= |expPostFix| &&
// 	exists exp':Expression :: ValueOf(exp')==ValueOf(exp) && Postfix(exp') == IntToOperands(stack) + expPostFix[i..]   
// }

// function IntToOperands(stack:seq<int>) : seq<Op>
// {
// 	if |stack| == 0 then []
// 	else [Operand(stack[0])] + IntToOperands(stack[1..])
// }

// lemma {:verify false} Lemma1Element(stack: seq<int>)
// 	ensures |stack| >= 1
// lemma {:verify false} Lemma2Elements(stack: seq<int>)
// 	ensures |stack| >= 2

method {:verify true} EvaluateIter(exp: Expression) returns (val: int)
	ensures val == ValueOf(exp)
{
	var stack: seq<Op>, i: nat, addOps: int, mulOps: int := [], 0, 0, 0;
	var expPostFix := ComputePostfixIter(exp);
	while i < |expPostFix|
		invariant Inv5(exp, stack, expPostFix, i)
		decreases |expPostFix| - i
	{
		var stack0 := stack;
		match expPostFix[i]{
			case Operand(x)     => stack := stack + [Operand(x)];
			case Addition       => Lemma2Elements(stack); addOps := addOperands(stack[|stack|-1] , stack[|stack|-2]); stack := stack[..|stack|-2] + [Operand(addOps)];
			case Multiplication => Lemma2Elements(stack); mulOps := multiplyOperands(stack[|stack|-1] , stack[|stack|-2]); stack := stack[..|stack|-2] + [Operand(mulOps)];
		}
		i := i + 1;
		LemmaInv(exp, stack0, stack, expPostFix, i);
	}
	Lemma1Element(stack);
	val := getValue(stack[0]);
	LemmaStrength(exp, stack, expPostFix, i, val);
}

lemma {:verify false} LemmaInv(exp: Expression, stack0: seq<Op>, stack: seq<Op>, expPostFix: seq<Op>, i:nat)
	//requires Inv5(exp, stack0, expPostFix, i-1) && i-1 < |expPostFix|
	ensures Inv5(exp, stack, expPostFix, i)
	decreases |expPostFix| - i 
{}

lemma {:verify false} LemmaStrength(exp: Expression, stack: seq<Op>, expPostFix: seq<Op>, i:nat, val: int)
	requires Inv5(exp, stack, expPostFix, i) && i == |expPostFix|
	ensures val == ValueOf(exp)
{}

predicate Inv5(exp: Expression, stack: seq<Op>, expPostFix: seq<Op>, i:nat)
{
	0 <= i <= |expPostFix| &&
	(forall k:nat :: 0 <= k < |stack| ==> stack[k] != Addition && stack[k] != Multiplication) && //stack contains only Operands 
	exists exp':Expression :: ValueOf(exp')==ValueOf(exp) && Postfix(exp') == stack + expPostFix[i..]  
	//value(stack + expPostFix[i..]) == value(satck0 + expPostFix[i-1..])
}

method addOperands(arg1: Op, arg2: Op) returns (result: int)
	requires arg1 != Addition && arg1 != Multiplication
	requires arg2 != Addition && arg2 != Multiplication
{
	var res1 := getValue(arg1);
	var res2 := getValue(arg2);
	result := res1 + res2;
}

method multiplyOperands(arg1: Op, arg2: Op) returns (result: int)
	requires arg1 != Addition && arg1 != Multiplication
	requires arg2 != Addition && arg2 != Multiplication
{
	var res1 := getValue(arg1);
	var res2 := getValue(arg2);
	result := res1 * res2;
}

method getValue(arg: Op) returns (value: int)
	requires arg != Addition && arg != Multiplication
{
	match arg{
		case Operand(x) => value := x;
	}
}

lemma {:verify false} Lemma1Element(stack: seq<Op>)
	ensures |stack| == 1
{}

lemma {:verify false} Lemma2Elements(stack: seq<Op>)
	ensures |stack| >= 2
{}

function valueOfPostFix(postFix: seq<Op>, l: nat, r:nat) : int
	requires 0 <= l <= r < |postFix| 
	decreases r - l
{
	match postFix[r]{
		case Operand(x) => x
		case Addition => var k := getSeparator(postFix,r-1,0,0); valueOfPostFix(postFix,l,k-1) + valueOfPostFix(postFix,k,r)
		case Multiplication => var k := getSeparator(postFix,r-1,0,0); valueOfPostFix(postFix,l,k-1) * valueOfPostFix(postFix,k,r)
	}
}

function getSeparator(postFix: seq<Op>, i:nat, Operands: nat, Operators: nat): nat
	requires 0 <= i < |postFix| 
	decreases i
{
	if i==0 then 0 
	else match postFix[i]{
		case Operand(x) => if Operands == Operators then i else getSeparator(postFix, i-1, Operands+1, Operators)  
		case Addition => getSeparator(postFix, i-1, Operands, Operators+1)
		case Multiplication => getSeparator(postFix, i-1, Operands, Operators+1)
	}
}

/*
שאלות לשעות קבלה
ניסינו לממש את האלגוריתם המוכר עם המחסנית
האינווריאנטה שלנו היא שמירה של הערך שיש בשרשור
stack + expPostFix[i..]
ואנחנו לא מצליחים להגדיר פונקציה שמקבלת 
seq<Op>
ומחזירה את הערך שהוא מייצג
ישבנו על זה ימים שלמים וניסינו 2 אלגוריתמים שונים וכמה אינווריאנטות שונות..
*/

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
// TODO: implement and document ALL steps of refinement (REC)
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


// TODO: complete the implementation (of LoopBody below) and the verification
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