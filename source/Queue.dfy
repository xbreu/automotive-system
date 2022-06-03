class {:autocontracts} Queue<T>
{
	const initializer : nat -> T;
	ghost var elemSeq : seq<T>;
	var elements : array<T>;
	var used : nat;
	
	constructor(default : T)
		ensures |elemSeq| == 0
		ensures elemSeq == []
		ensures used == 0
	{
		initializer := (_) => default;
		elemSeq := [];
		used := 0;
		new;
		elements := new T[1](initializer);
	}

	predicate Valid()
	{
		&& used <= elements.Length
		&& elemSeq == elements[..used]
		&& elements.Length > 0 
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
	{
		var oldArray := elements;
		elements := new T[2 * elements.Length + 1](initializer);
		forall i | 0 <= i < used
		{
			elements[i] := oldArray[i];
		}
		assert elements[..used] == old(elements[..used]);
	}

	method push(value : T) returns ()
		ensures elemSeq == old(elemSeq) + [value]
	{
		if used == elements.Length {
			grow();
		}
		elements[used] := value;
		used := used + 1;
		elemSeq := elemSeq + [value];
	}

	method pop() returns (value : T)
		requires !empty()
		ensures value == old(elemSeq[0])
		ensures elemSeq == old(elemSeq[1..])
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

	static method create(default : T) returns (instance : Queue<T>)
		ensures fresh(instance)
		ensures |instance.elemSeq| == 0
		ensures instance.used == 0
		ensures instance.Valid()
	{
		instance := new Queue<T>(default);
	}
}

method TestQueue()
{
	var x := new Queue<int>(0);
	x.push(2);
	// assert x.size() == 1;
	x.push(3);
	// assert x.size() == 2;
	var y := x.pop();
	// assert x.size() == 1;
	// assert y == 2;
	y := x.pop();
	assert x.size() == 0;
	assert y == 3;
}
