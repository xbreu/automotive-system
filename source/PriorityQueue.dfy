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
	var queues : array<Queue<T>>;
	ghost var sequences : seq<seq<T>>;

	constructor(maxPriority : nat, default : nat -> Queue<T>)
		ensures this.maxPriority == maxPriority
		ensures sequences == emptyLists(maxPriority)
		ensures queues.Length == maxPriority
	{
		this.maxPriority := maxPriority;
		new;
		this.queues := new Queue<T>[maxPriority](default);
		this.sequences := emptyLists(maxPriority);
	}

	predicate Valid()
	{
		&& |sequences| == maxPriority
		&& queues.Length == maxPriority
		&& forall i :: 0 <= i < |sequences| ==> sequences[i] == queues[i].elemSeq	
	}

	method size() returns (result : nat)
		ensures result == |flatten(sequences)|
	{
		result := 0;
		forall i | 0 <= i < queues.Length
		{
			result := result + queues[i].size();
		}
	}

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
		
	method empty() returns (result : bool)
		ensures result <==> (|flatten(sequences)| == 0)
	{
		var size := size();
		result := (size == 0);
	}

	function minPriority() : nat
		requires |flatten(sequences)| > 0
		ensures 0 < minPriority() <= maxPriority
		ensures |sequences[index(minPriority())]| > 0
		ensures forall k :: 0 <= k < |sequences| && sequences[k] != []
		==> index(minPriority()) <= k

	method push(value : T, priority : nat)
		requires 0 < priority <= maxPriority
		ensures sequences[index(priority)] == old(sequences[index(priority)]) + [value]
		// ensures size() == old(size()) + 1
		ensures forall k :: 0 <= k < |sequences| && k != index(priority)
		==> sequences[k] == old(sequences[k])

	method pop() returns (result : T)
		requires |flatten(sequences)| > 0
		ensures result == old(sequences[index(minPriority())][0])
		ensures sequences[old(index(minPriority()))] == old(sequences[index(minPriority())][1..])
		// ensures size() == old(size()) - 1
		ensures forall k :: 0 <= k < |sequences| && k != old(index(minPriority()))
		==> sequences[k] == old(sequences[k])
}

method TestPriorityQueue()
{
	var initializer : nat -> Queue<int> := (_) => (new Queue<int>(0));
	var a := new Queue<int>(0);
	var q := new PriorityQueue<int>(3, initializer);
	q.push(2, 1);
	q.push(-3, 3);
	q.push(5, 2);
	var y := q.pop();
	assert y == 2;
	y := q.pop();
	assert y == 5;
	y := q.pop();
	assert y == -3;
}
