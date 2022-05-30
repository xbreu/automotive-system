class {:autocontracts} PriorityQueue<T> {
	var sequence : seq<(nat, T)>;

	constructor()
	{
		sequence := [];
	}

	predicate Valid()
	{
		// The priorities follow an order
		true
		// isOrdered()
	}

	predicate isOrdered() 
	{
		forall i, j :: 0 <= i < j < size() ==> sequence[i].0 <= sequence[j].0
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
	requires isOrdered()
	ensures isOrdered()
	ensures size() == old(size()) + 1
	{
		var i := 0;
		while i < size()
		invariant 0 <= i <= size()
		invariant isOrdered()
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

	method pop()
	{
		
	}

	method peek()
	{
		
	}
}
