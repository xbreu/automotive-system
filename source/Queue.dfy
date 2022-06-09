include "Signal.dfy"

class {:autocontracts} Queue
{
	const initializer : nat -> Signal;
	ghost var elemSeq : seq<Signal>;
	var elements : array<Signal>;
	var used : nat;
	
	constructor(default : Signal)
		ensures |elemSeq| == 0
		ensures elemSeq == []
		ensures used == 0
		ensures fresh(elements)
	{
		initializer := (_) => default;
		elemSeq := [];
		used := 0;
		new;
		elements := new Signal[1](initializer);
	}

	predicate Valid()
		reads this`used
		reads this.elements
		reads this`Repr
	{
		&& used <= elements.Length
		&& elemSeq == elements[..used]
		&& elements.Length > 0
		&& Repr == {this, elements}
	}

	function method size() : nat
		ensures size() == |elemSeq|
	{
		used
	}

	predicate method empty()
		ensures empty() <==> (|elemSeq| == 0)
	{
		used == 0
	}

	method grow()
		ensures elemSeq == old(elemSeq)
		ensures elements.Length > old(elements.Length)
		ensures fresh(elements)
	{
		var oldArray := elements;
		elements := new Signal[2 * elements.Length + 1](initializer);
		forall i | 0 <= i < used
		{
			elements[i] := oldArray[i];
		}
		// assert elements[..used] == old(elements[..used]);
		Repr := {this, elements};
	}

	method push(value : Signal) returns ()
		ensures elemSeq == old(elemSeq) + [value]
		ensures elements == old(elements) || fresh(elements)
	{
		if used == elements.Length {
			grow();
		}
		elements[used] := value;
		used := used + 1;
		elemSeq := elemSeq + [value];
	}

	method pop() returns (value : Signal)
		modifies this.elements
		modifies this`used
		modifies this`elemSeq
		requires !empty()
		ensures value == old(elemSeq[0])
		ensures elemSeq == old(elemSeq[1..])
		ensures Repr == old(Repr)
		ensures elements == old(elements)
	{
		value := elements[0];
		used := used - 1;
		var oldArray := elements;
		forall i | 0 <= i < used
		{
			elements[i] := oldArray[i + 1];
		}
		elemSeq := elemSeq[1..];
	}

	function method peek() : Signal
		requires !empty()
	{
		elements[0]
	}
}

method TestQueue()
{
	var x := new Queue(Reverse(false));

	x.push(Brake(2));
	assert x.size() == 1;

	x.push(Voltage(5));
	assert x.size() == 2;

	var y := x.pop();
	assert x.size() == 1;
	assert y == Brake(2);

	y := x.peek();
	assert y == Voltage(5);

	y := x.pop();
	assert x.size() == 0;
	assert y == Voltage(5);
}
