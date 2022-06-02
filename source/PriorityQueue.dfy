predicate isSortedSub<T>(sequence : seq<(nat, T)>, start : nat, end : nat)
	requires end <= |sequence|
{
	forall i, j :: start <= i < j < end ==> sequence[i].0 <= sequence[j].0
}

predicate isSorted<T>(sequence : seq<(nat, T)>)
{
	isSortedSub<T>(sequence, 0, |sequence|)
}

predicate allLessPriority<T>(sequence : seq<(nat, T)>, start : nat, end : nat, priority : nat)
	requires end <= |sequence|
{
	forall j :: start <= j < end ==> sequence[j].0 <= priority
}

class {:autocontracts} PriorityQueue<T> {
	var sequence : seq<(nat, T)>;

	constructor()
	{
		sequence := [];
	}

	predicate Valid()
	{
		// The priorities follow an order
		isSorted(sequence)
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
		ensures size() == old(size()) + 1
	{
		var i := 0;
		while i < size()
			invariant 0 <= i <= size()
			invariant allLessPriority(sequence, 0, i, priority)
			invariant isSorted(sequence)
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

method TestPriorityQueue()
{
	var x := new PriorityQueue<nat>();
	x.add(1, 3);
	x.add(2, 5);
	x.add(1, 4);
	x.add(2, 3);
	var y := x.pop();
	assert y == 3;
	y := x.pop();
	assert y == 4;
	y := x.pop();
	assert y == 5;
	y := x.pop();
	assert y == 3;
}
