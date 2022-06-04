include "Signal.dfy"
include "Queue.dfy"

const maxPriority := 3;

function emptyLists<T>() : seq<seq<T>>
	ensures |emptyLists<T>()| == maxPriority
	ensures forall i :: 0 <= i < maxPriority ==> emptyLists<T>()[i] == []
	ensures flatten(emptyLists<T>()) == []
{
	[[], [], []]
}

function flatten<T>(sequences : seq<seq<T>>) : seq<T>
	requires |sequences| == maxPriority
{
	sequences[0] + sequences[1] + sequences[2]
}

function firstNonEmpty<T>(sequences : seq<seq<T>>) : nat
	requires |sequences| == maxPriority
	requires flatten(sequences) != []
	ensures 0 <= firstNonEmpty(sequences) < |sequences|
	ensures |sequences[firstNonEmpty(sequences)]| > 0
	ensures forall k :: 0 <= k < |sequences| && sequences[k] != []
	==> firstNonEmpty(sequences) <= k
{
	assert sequences[0] != [] || sequences[1] != [] || sequences[2] != [];
	if sequences[0] != [] then
		0
	else if sequences[1] != [] then
		1
	else
		2
}

function addTo<T>(sequences : seq<seq<T>>, priority : nat, value : T) : seq<seq<T>>
	requires 0 < priority <= maxPriority
	requires |sequences| == maxPriority
	ensures |addTo(sequences, priority, value)| == maxPriority
	ensures forall i :: 0 <= i < maxPriority && i != index(priority) ==> addTo(sequences, priority, value)[i] == sequences[i]
	ensures addTo(sequences, priority, value)[index(priority)] == sequences[index(priority)] + [value] 
{
	var changeIndex := index(priority);
	var seq0 := if changeIndex == 0 then
		sequences[0] + [value]
	else
		sequences[0];
		var seq1 := if changeIndex == 1 then
			sequences[1] + [value]
		else
			sequences[1];
			var seq2 := if changeIndex == 2 then
				sequences[2] + [value]
	else
		sequences[2];
		[seq0, seq1, seq2]
}

function removeFrom<T>(sequences : seq<seq<T>>, priority : nat) : seq<seq<T>>
	requires 0 < priority <= maxPriority
	requires |sequences| == maxPriority
	requires |sequences[index(priority)]| > 0 
	ensures |removeFrom(sequences, priority)| == maxPriority
	ensures forall i :: 0 <= i < maxPriority && i != index(priority) ==> removeFrom(sequences, priority)[i] == sequences[i]
	ensures removeFrom(sequences, priority)[index(priority)] == sequences[index(priority)][1..]
{
	var changeIndex := index(priority);
	var seq0 := if changeIndex == 0 then
		sequences[0][1..]
	else
		sequences[0];
		var seq1 := if changeIndex == 1 then
			sequences[1][1..]
	else
		sequences[1];
		var seq2 := if changeIndex == 2 then
			sequences[2][1..]
	else
		sequences[2];
		[seq0, seq1, seq2]
}

function method index(priority : nat) : nat
	requires 0 < priority <= maxPriority
	ensures 0 <= index(priority) < maxPriority
{
	priority - 1
}

function priority(index : nat) : nat
	requires 0 <= index < maxPriority
	ensures 0 < priority(index) <= maxPriority
{
	index + 1
}


class {:autocontracts} PriorityQueue
{
	var queue0 : Queue;
	var queue1 : Queue;
	var queue2 : Queue;
	var elements : nat;
	ghost var sequences : seq<seq<Signal>>;

	constructor(default : Signal)
		ensures sequences == emptyLists()
		ensures flatten(sequences) == []
	{
		this.elements := 0;
		this.queue0 := new Queue(default);
		this.queue1 := new Queue(default);
		this.queue2 := new Queue(default);
		this.sequences := emptyLists();
	} 

	predicate Valid()
	{
		&& |sequences| == maxPriority
		&& elements == |flatten(sequences)|
		&& queue0.Valid()
		&& queue1.Valid()
		&& queue2.Valid()
		&& queue0 != queue1
		&& queue1 != queue2
		&& queue2 != queue0
		&& queue0.elements != queue1.elements
		&& queue1.elements != queue2.elements
		&& queue2.elements != queue0.elements
		&& queue0.Repr * queue1.Repr == {}
		&& queue1.Repr * queue2.Repr == {}
		&& queue2.Repr * queue0.Repr == {}
		&& sequences[0] == queue0.elemSeq
		&& sequences[1] == queue1.elemSeq
		&& sequences[2] == queue2.elemSeq	
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
		if queue0.size() > 0 {
			min := 1;
		} else if queue1.size() > 0 {
			min := 2;
		} else {
			min := 3;
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
		if queueIndex == 0 {
			queue0.push(value);
		} else if queueIndex == 1 {
			queue1.push(value);
		} else if queueIndex == 2 {
			queue2.push(value);
		}

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
		
		if queueIndex == 0 {
			result := queue0.pop();
		} else if queueIndex == 1 {
			result := queue1.pop();
		} else if queueIndex == 2 {
			result := queue2.pop();
		}

		elements := elements - 1;
		sequences := removeFrom(sequences, priority);
	}

	method peek() returns (result : Signal)
		requires !empty()
		ensures result == old(sequences[index(minPriorityFunc())][0])
		ensures sequences == old(sequences)
	{
		var priority := minPriority();
		var queueIndex := index(priority);
		
		if queueIndex == 0 {
			result := queue0.peek();
		} else if queueIndex == 1 {
			result := queue1.peek();
		} else if queueIndex == 2 {
			result := queue2.peek();
		}
	}
}

method TestPriorityQueue()
{
	var q := new PriorityQueue(Reverse(false));
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
