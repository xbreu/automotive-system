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
	}

	function method size() : nat
	{
		|sequence|
	}
	
	predicate method empty()
	{
		|sequence| == 0
	}
	
	method add(element : T, priority : nat)
	{

	}

	method pop()
	{
		
	}

	method peek()
	{
		
	}
}
