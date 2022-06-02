include "Queue.dfy"

function method emptyLists<T>(size : nat) : seq<seq<T>>
	ensures |emptyLists<T>(size)| == size
	ensures forall i :: 0 <= i < size ==> emptyLists<T>(size)[i] == []
{
	if size == 0 then
		[]
	else
		[[]] + emptyLists(size - 1)
}

function method flatten<T>(sequences : seq<seq<T>>) : seq<T>
{
	if sequences == [] then
		[]
	else
		sequences[0] + flatten(sequences[1..])
}

class {:autocontracts} PriorityQueue<T>
{
	const maxPriority : nat;
	ghost var sequences : seq<seq<T>>;
	
	constructor(maxPriority : nat)
		ensures this.maxPriority == maxPriority
		ensures sequences == emptyLists(maxPriority)
	{
		this.maxPriority := maxPriority;
		this.sequences := emptyLists(maxPriority);
	}

	predicate Valid()
	{
		|sequences| == maxPriority
	}

	function method size() : nat
		ensures size() == |flatten(sequences)|

	function index(priority : nat) : nat
		requires 0 < priority <= maxPriority
		ensures 0 <= index(priority) < |sequences|
	{
		priority - 1
	}

	function priority(index : nat) : nat
		requires 0 <= index < |sequences|
		ensures 0 < priority(index) <= maxPriority
	{
		index + 1
	}
		
	predicate method empty()
		ensures empty() <==> (|flatten(sequences)| == 0)

	function minPriority() : nat
		requires !empty()
		ensures 0 < minPriority() <= maxPriority
		ensures |sequences[index(minPriority())]| > 0
		ensures forall k :: 0 <= k < |sequences| && sequences[k] != []
		==> index(minPriority()) <= k

	method push(value : T, priority : nat)
		requires 0 < priority <= maxPriority
		ensures sequences[index(priority)] == old(sequences[index(priority)]) + [value]
		ensures forall k :: 0 <= k < |sequences| && k != index(priority)
		==> sequences[k] == old(sequences[k])

	method pop() returns (result : T)
		requires !empty()
		ensures result == old(sequences[index(minPriority())][0])
		ensures sequences[old(index(minPriority()))] == old(sequences[index(minPriority())][1..])
		ensures forall k :: 0 <= k < |sequences| && k != old(index(minPriority()))
		==> sequences[k] == old(sequences[k])
}

method TestPriorityQueue()
{
	var q := new PriorityQueue<int>(3);
	q.push(2, 1);
	q.push(-3, 3);
	q.push(5, 2);
	var y := q.pop();
	assert y == 2;
}
