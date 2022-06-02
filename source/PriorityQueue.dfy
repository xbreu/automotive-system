class {:autocontracts} PriorityQueue<T> {
	var sequence : seq<(nat, T)>;

	constructor()
	{
		sequence := [];
	}

	predicate Valid()
	{
		// The priorities follow an order
		forall i, j :: 0 <= i < j < |sequence| ==> sequence[i].0 <= sequence[j].0
	}

	predicate isOrdered(sequence : seq<(nat, T)>)
	{
		forall i, j :: 0 <= i < j < |sequence| ==> sequence[i].0 <= sequence[j].0
	}

	function method size() : nat
	{
		|sequence|
	}
	
	predicate method empty()
	{
		|sequence| == 0
	}
	
	method add(priority : nat, element : T)
	requires isOrdered(sequence)
	ensures isOrdered(sequence)
	ensures size() == old(size()) + 1
	{
		var i := 0;
		while i < size()
			invariant 0 <= i <= size()
			invariant forall j :: 0 <= j < i ==> sequence[j].0 <= priority
			invariant isOrdered(sequence)
			decreases size() - i
		{
			if priority < sequence[i].0
			{
				sequence :=  sequence[..i] + [(priority, element)] + sequence[i..];
				return;
			}
			i := i + 1;
		}
    sequence :=  sequence + [(priority, element)];
	}

	method pop() returns (x : T)
		requires !empty()
		ensures size() == old(size()) - 1
		ensures sequence == old(sequence[1..])
	{
		x := peek();
		sequence := sequence[1..];
	}

	method peek() returns (x : T)
		requires !empty()
		ensures sequence == old(sequence)
	{
		var item := sequence[0];
		x := item.1;
	}
}
