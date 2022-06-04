include "Signal.dfy"
include "Queue.dfy"

function emptyLists<T>(size : nat) : seq<seq<T>>
	ensures |emptyLists<T>(size)| == size
	ensures forall i :: 0 <= i < size ==> emptyLists<T>(size)[i] == []
	ensures flatten<T>(emptyLists<T>(size)) == []
{
	if size == 0 then
		[]
	else
		[[]] + emptyLists(size - 1)
}

function flatten<T>(sequences : seq<seq<T>>) : seq<T>
{
	if |sequences| == 0 then
		[]
	else
		sequences[0] + flatten(sequences[1..])
}

function firstNonEmpty<T>(sequences : seq<seq<T>>) : nat
	requires flatten<T>(sequences) != []
	ensures 0 <= firstNonEmpty<T>(sequences) < |sequences|
	ensures |sequences[firstNonEmpty<T>(sequences)]| > 0
	ensures forall k :: 0 <= k < |sequences| && sequences[k] != []
	==> firstNonEmpty<T>(sequences) <= k
{
	if sequences[0] != [] then
		0
	else
		1 + firstNonEmpty(sequences[1..])
}

function addTo<T>(sequences : seq<seq<T>>, priority : nat, value : T) : seq<seq<T>>
	requires 0 < priority <= |sequences|
	ensures |addTo(sequences, priority, value)| == |sequences|
	ensures forall i :: 0 <= i < |sequences| && i != index(priority) ==> addTo(sequences, priority, value)[i] == sequences[i]
	ensures addTo(sequences, priority, value)[index(priority)] == sequences[index(priority)] + [value] 
{
	var changeIndex := index(priority);
	if changeIndex == 0 then
		[sequences[0] + [value]] + sequences[1..]
	else
		[sequences[0]] + addTo(sequences[1..], priority - 1, value)
}

function removeFrom<T>(sequences : seq<seq<T>>, priority : nat) : seq<seq<T>>
	requires 0 < priority <= |sequences|
	requires |sequences[index(priority)]| > 0 
	ensures |removeFrom(sequences, priority)| == |sequences|
	ensures forall i :: 0 <= i < |sequences| && i != index(priority) ==> removeFrom(sequences, priority)[i] == sequences[i]
	ensures removeFrom(sequences, priority)[index(priority)] == sequences[index(priority)][1..]
{
	var changeIndex := index(priority);
	if changeIndex == 0 then
		[sequences[0][1..]] + sequences[1..]
	else
		[sequences[0]] + removeFrom(sequences[1..], priority - 1)
}

function method index(priority : nat) : nat
	requires 0 < priority
	ensures 0 <= index(priority)
{
	priority - 1
}

function priority(index : nat) : nat
	ensures 0 < priority(index)
{
	index + 1
}


class {:autocontracts} PriorityQueue
{
	const maxPriority : nat;
	var queues : array<Queue>;
	var elements : nat;
	ghost var sequences : seq<seq<Signal>>;

	constructor(maxPriority : nat, default : Signal)
		requires maxPriority > 0
		ensures sequences == emptyLists(maxPriority)
		ensures flatten(sequences) == []
		ensures this.maxPriority == maxPriority
	{
		this.maxPriority := maxPriority;
		new;
		var dummyQueue := new Queue(default);
		var queuesI : array<Queue> := new Queue[maxPriority](_ => dummyQueue);
		var i := 0;
		while i < maxPriority
			invariant 0 <= i <= maxPriority
			invariant forall j :: 0 <= j < i ==> queuesI[j].Valid()
			invariant forall j :: 0 <= j < i ==> queuesI[j].elemSeq == []
			invariant forall j, k :: 0 <= j < k < i ==> queuesI[j] != queuesI[k]
			invariant forall j, k :: 0 <= j < k < i ==> queuesI[j].elements != queuesI[k].elements
		{
			queuesI[i] := new Queue(default);
			i := i + 1;
		}
		queues := queuesI;
		this.elements := 0;
		this.sequences := emptyLists(maxPriority);
		assert |sequences| == maxPriority;
		assert elements == |flatten(sequences)|;
		assert forall i :: 0 <= i < maxPriority ==> queues[i].Valid();
		assert forall i, j :: 0 <= i < j < maxPriority ==> queues[i] != queues[j];
		assert forall i :: 0 <= i < maxPriority ==> sequences[i] == queues[i].elemSeq;
		assert forall i, j :: 0 <= i < j < maxPriority ==> queues[i].elements != queues[j].elements;
	}

	predicate Valid()
	{
		&& |sequences| == maxPriority
		&& queues.Length == maxPriority
		&& elements == |flatten(sequences)|
		&& (forall i :: 0 <= i < maxPriority ==> queues[i].Valid())
		&& (forall i, j :: 0 <= i < j < maxPriority ==> queues[i] != queues[j])
		&& (forall i, j :: 0 <= i < j < maxPriority ==> queues[i].elements != queues[j].elements)
		&& (forall i, j :: 0 <= i < j < maxPriority ==> queues[i].Repr * queues[j].Repr == {})
		&& (forall i :: 0 <= i < maxPriority ==> sequences[i] == queues[i].elemSeq)
	}
	
	function method size() : nat
		ensures size() == |flatten(sequences)|
	{
		elements
	}
		
	predicate method empty()
		ensures empty() <==> (size() == 0)
	{
		size() == 0
	}

	function minPriorityFunc() : nat
		requires !empty()
		ensures 0 < minPriorityFunc() <= maxPriority
		ensures |sequences[index(minPriorityFunc())]| > 0
		ensures forall k :: 0 <= k < |sequences| && sequences[k] != []
		==> index(minPriorityFunc()) <= k
	{
		priority(firstNonEmpty(sequences))
	}
	
	method minPriority() returns (min : nat)
		requires !empty()
		ensures min == minPriorityFunc()
		ensures 0 < min <= maxPriority
		ensures |sequences[index(min)]| > 0
		ensures forall k :: 0 <= k < |sequences| && sequences[k] != []
		==> index(min) <= k
	{
		var i := 0;
		while i < maxPriority
			invariant 0 <= i <= maxPriority
			invariant forall j :: 0 <= j < i ==> queues[j].size() == 0
		{
			if queues[i].size() > 0
			{
				min := i + 1;
				break;
			}
			i := i + 1;
		}
	}
	
	method push(value : Signal, priority : nat)
		requires 0 < priority <= maxPriority
		ensures sequences[index(priority)] == old(sequences[index(priority)]) + [value]
		ensures size() == old(size()) + 1
		ensures forall k :: 0 <= k < |sequences| && k != index(priority)
		==> sequences[k] == old(sequences[k])
	{
		var queueIndex := index(priority);
		queues[queueIndex].push(value);
		elements := elements + 1;
		sequences := addTo(sequences, priority, value);
	}

	method pop() returns (result : Signal)
		requires !empty()
		ensures result == old(sequences[index(minPriorityFunc())][0])
		ensures sequences[old(index(minPriorityFunc()))] == old(sequences[index(minPriorityFunc())][1..])
		ensures size() == old(size()) - 1
		ensures forall k :: 0 <= k < |sequences| && k != old(index(minPriorityFunc()))
		==> sequences[k] == old(sequences[k])
	{
		var priority := minPriority();
		var queueIndex := index(priority);
		result := queues[queueIndex].pop();
		elements := elements - 1;
		sequences := removeFrom(sequences, priority);
	}

	method peek() returns (result : Signal)
		requires !empty()
		ensures result == sequences[index(minPriorityFunc())][0]
	{
		var priority := minPriority();
		var queueIndex := index(priority);
		result := queues[queueIndex].peek();
	}
}

/*
method TestPriorityQueue()
{
	var q := new PriorityQueue(3, Reverse(false));
	q.push(Brake(2), 1);
	q.push(Beam(20), 3);
	q.push(Brake(5), 2);
	var y := q.pop();
	assert y == Brake(2);
	y := q.peek();
	assert y == Brake(5);
	y := q.pop();
	assert y == Brake(5);
	y := q.pop();
	assert y == Beam(20);
}*/
