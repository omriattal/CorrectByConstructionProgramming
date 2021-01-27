datatype Expression = Value(int) | Add(Expression,Expression) | Multiply(Expression,Expression)
datatype Op = Operand(int) | Addition | Multiplication

method Main() {
	var exp := Add(Value(7),Multiply(Value(3),Value(5)));
	print "\nThe value of Add(Value(7),Multiply(Value(3),Value(5))) is ";
	var x := Evaluate(exp);
	print x;
	assert x == 7 + 3*5;

	// x := EvaluateIter(exp); // evaluate iteratively this time, instead of recursively
	// assert x == 7 + 3*5;
	// print "\nThe iteratively-computed value of Add(Value(7),Multiply(Value(3),Value(5))) is ";
	// print x;
	
	var postfix;// := ComputePostfix(exp);
	// print "\nThe postfix form of Add(Value(7),Multiply(Value(3),Value(5))) is ";
	// print postfix;
	// assert postfix == [Operand(7),Operand(3),Operand(5),Multiplication,Addition];
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

// TODO: implement iteratively (not recursively), using a loop;
// if it helps, feel free to use ComputePostfix or ComputePostfixIter;
// NO NEED to document the steps of refinement
// method EvaluateIter(exp: Expression) returns (val: int)
// 	ensures val == ValueOf(exp)

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
// method ComputePostfix(exp: Expression) returns (res: seq<Op>)
// 	ensures res == Postfix(exp)
// 	decreases exp

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
		assert stackToOps(stack) == stackToOps(stack[..|stack|-2]) + Postfix(l)+Postfix(r) by{L1(stack,l,r);}
		assert stackToOps(stack) + ops == Postfix(exp);
	}
	assert V(stack) < V(stack0) by{
		assert StackSize(stack) < StackSize(stack0) by{
			L2(stack,stack0,popped,l,r);
		}
	}
}

lemma LemmaMul(exp: Expression, stack0: seq<Expression>, ops0: seq<Op>, stack: seq<Expression>, ops: seq<Op>, popped: Expression, l:Expression, r:Expression)
	requires Inv(exp, stack0, ops0) && stack0 != [] && popped == Multiply(l,r) && popped == stack0[|stack0|-1]
	requires ops == [Multiplication] + ops0 && stack == stack0[..|stack0|-1] + [l,r]
	ensures Inv(exp, stack, ops) && 0 <= V(stack) < V(stack0)
{
	assert Inv(exp, stack, ops) by{
		assert stackToOps(stack) == stackToOps(stack[..|stack|-2]) + Postfix(l)+Postfix(r) by{L1(stack,l,r);}
		assert stackToOps(stack) + ops == Postfix(exp);
	}
	assert 0 <= V(stack) < V(stack0) by {
			assert StackSize(stack) < StackSize(stack0) by {
			L2(stack,stack0,popped,l,r);
		}
	}
}

lemma L1(stack:seq<Expression>,l:Expression, r:Expression)
	requires |stack| >= 2 && stack == stack[..|stack|-2] + [l,r]
	ensures stackToOps(stack) == stackToOps(stack[..|stack|-2]) + Postfix(l) + Postfix(r);
{
	assert stackToOps(stack) == stackToOps(stack[..|stack|-1]) + Postfix(stack[|stack|-1]);
	assert stackToOps(stack) == stackToOps(stack[..|stack|-1]) + Postfix(r);
	assert stack[..|stack|-1] == stack[..|stack|-2] + [stack[|stack|-2]];
	assert stackToOps(stack[..|stack|-1]) == stackToOps(stack[..|stack|-2]) + Postfix(stack[|stack|-2]);
	assert stackToOps(stack[..|stack|-2]) + Postfix(l)+Postfix(r) == stackToOps(stack);
}
lemma L2(stack:seq<Expression>,stack0:seq<Expression>,popped:Expression,l:Expression, r:Expression)
	requires |stack0|>= 1 && stack == stack0[..|stack0|-1] + [l,r] && (popped == Multiply(l,r) || popped == Add(l,r)) && popped == stack0[|stack0|-1]
	ensures StackSize(stack) < StackSize(stack0)
{
	assert stack0 == stack0[..|stack0|-1] + [popped];
	assert StackSize(stack0) == StackSize(stack0[..|stack0|-1]) + StackSize( [popped]);
	assert stack  == stack0[..|stack0|-1] + [l] + [r];
	assert StackSize(stack) == StackSize(stack0[..|stack0|-1] + [l]) + StackSize( [r]);
	assert StackSize(stack0[..|stack0|-1] + [l]) == StackSize(stack0[..|stack0|-1]) + StackSize([l]);
	assert ExpressionSize(popped) > ExpressionSize(l) + ExpressionSize(r);
}