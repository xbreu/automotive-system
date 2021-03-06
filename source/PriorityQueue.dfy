include "Signal.dfy"
include "Queue.dfy"
include "Utils.dfy"

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
		ensures fresh(queues)
		ensures forall i :: 0 <= i < maxPriority ==> fresh(queues[i])
		ensures forall i :: 0 <= i < maxPriority ==> fresh(queues[i].elements)
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
			invariant forall j :: 0 <= j < i ==> fresh(queuesI[j])
			invariant forall j :: 0 <= j < i ==> fresh(queuesI[j].elements)
			invariant forall j, k :: 0 <= j < k < i ==> queuesI[j] != queuesI[k]
			invariant forall j, k :: 0 <= j < k < i ==> queuesI[j].elements != queuesI[k].elements
		{
			queuesI[i] := new Queue(default);
			i := i + 1;
		}
		queues := queuesI;
		this.elements := 0;
		this.sequences := emptyLists(maxPriority);
	}

	predicate Valid()
		reads this.queues
		reads set i | 0 <= i < queues.Length :: queues[i]
		reads set i | 0 <= i < queues.Length :: queues[i].elements
		reads set i | 0 <= i < queues.Length :: queues[i]`used
		reads set x, y | y in (set i | 0 <= i < queues.Length :: queues[i].Repr) && x in y :: x
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
		reads this`elements
		reads this`sequences
		reads this.queues
		reads this.Repr
		reads set i | 0 <= i < queues.Length :: queues[i]
		reads set i | 0 <= i < queues.Length :: queues[i].elements
		reads set i | 0 <= i < queues.Length :: queues[i]`used
		reads set x, y | y in (set i | 0 <= i < queues.Length :: queues[i].Repr) && x in y :: x
		ensures size() == |flatten(sequences)|
	{
		elements
	}
		
	predicate method empty()
		reads this`elements
		reads this`sequences
		reads this.queues
		reads this.Repr
		reads set i | 0 <= i < queues.Length :: queues[i]
		reads set i | 0 <= i < queues.Length :: queues[i].elements
		reads set i | 0 <= i < queues.Length :: queues[i]`used
		reads set x, y | y in (set i | 0 <= i < queues.Length :: queues[i].Repr) && x in y :: x
		ensures empty() <==> (size() == 0)
	{
		size() == 0
	}

	function minPriorityFunc() : nat
		reads this`elements
		reads this`sequences
		reads this.queues
		reads this.Repr
		reads set i | 0 <= i < queues.Length :: queues[i]
		reads set i | 0 <= i < queues.Length :: queues[i].elements
		reads set i | 0 <= i < queues.Length :: queues[i]`used
		reads set x, y | y in (set i | 0 <= i < queues.Length :: queues[i].Repr) && x in y :: x
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
		modifies this.queues
		modifies this`elements
		modifies this`sequences
		modifies set i | 0 <= i < queues.Length :: queues[i]
		modifies set i | 0 <= i < queues.Length :: queues[i].elements
		requires 0 < priority <= maxPriority
		ensures sequences[index(priority)] == old(sequences[index(priority)]) + [value]
		ensures size() == old(size()) + 1
		ensures queues == old(queues)
		ensures forall k :: 0 <= k < |sequences| && k != index(priority)
		  ==> sequences[k] == old(sequences[k])
		ensures forall i :: 0 <= i < queues.Length
		  ==> queues[i] == old(queues[i])
		ensures forall i :: 0 <= i < queues.Length
		  ==> queues[i].elements == old(queues[i].elements) || fresh(queues[i].elements)
	{
		var queueIndex := index(priority);
		queues[queueIndex].push(value);
		sequences := addTo(sequences, priority, value);
		elements := elements + 1;
	}

	method pop() returns (result : Signal)
		modifies queues
		modifies set i | 0 <= i < queues.Length :: queues[i]
		modifies set i | 0 <= i < queues.Length :: queues[i].elements
		modifies this`elements
		modifies this`sequences
		requires !empty()
		ensures result == old(sequences[index(minPriorityFunc())][0])
		ensures sequences[old(index(minPriorityFunc()))] == old(sequences[index(minPriorityFunc())][1..])
		ensures size() == old(size()) - 1
		ensures forall k :: 0 <= k < |sequences| && k != old(index(minPriorityFunc()))
		==> sequences[k] == old(sequences[k])
		ensures Repr == old(Repr)
		ensures forall i :: 0 <= i < queues.Length
		  ==> queues[i] == old(queues[i])
		ensures forall i :: 0 <= i < queues.Length
		  ==> queues[i].elements == old(queues[i].elements)
	{
		var priority := minPriority();
		var queueIndex := index(priority);
		result := queues[queueIndex].pop();
		elements := elements - 1;
		sequences := removeFrom(sequences, priority);
	}

	method peek() returns (result : Signal)
		requires !empty()
		ensures elements == old(elements)
		ensures sequences == old(sequences)
		ensures result == sequences[index(minPriorityFunc())][0]
		ensures forall i :: 0 <= i < queues.Length
		  ==> queues[i] == old(queues[i])
		ensures forall i :: 0 <= i < queues.Length
		  ==> queues[i].elements == old(queues[i].elements)
		ensures Repr == old(Repr)
	{
		var priority := minPriority();
		var queueIndex := index(priority);
		result := queues[queueIndex].peek();
	}
}

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
}
