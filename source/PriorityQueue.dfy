include "Queue.dfy"

function emptyLists<T>(size : nat) : seq<seq<T>>
	ensures |emptyLists<T>(size)| == size
	ensures forall i :: 0 <= i < size ==> emptyLists<T>(size)[i] == []
	ensures flatten(emptyLists<T>(size)) == []
{
	if size == 0 then
		[]
	else
		[[]] + emptyLists(size - 1)
}

function flatten<T>(sequences : seq<seq<T>>) : seq<T>
{
	if sequences == [] then
		[]
	else
		sequences[0] + flatten(sequences[1..])
}

lemma flattenNonEmptyImpliesSomeElement<T>(sequences : seq<seq<T>>)
	ensures flatten(sequences) != [] <==> exists i :: 0 <= i < |sequences| && sequences[i] != []
{
	if flatten(sequences) == [] {
		assert forall i :: 0 <= i < |sequences| ==> sequences[i] == [];
	} else if sequences[0] == [] {
		flattenNonEmptyImpliesSomeElement(sequences[1..]);
	} else {
		assert sequences[0] != [];
	}
}

function firstNonEmpty<T>(sequences : seq<seq<T>>) : nat
	requires flatten<T>(sequences) != []
	requires |sequences| > 0
	ensures 0 <= firstNonEmpty(sequences) < |sequences|
	ensures |sequences[firstNonEmpty(sequences)]| > 0
	ensures forall k :: 0 <= k < |sequences| && sequences[k] != []
	==> firstNonEmpty(sequences) <= k
	decreases |sequences|
{
	if sequences[0] != [] then
		0
	else
		1 + firstNonEmpty(sequences[1..])
}

const maxPriority := 3;

class {:autocontracts} PriorityQueue<T>
{
	// const maxPriority : nat;
	var queues : array<Queue<T>>;
	var elements : nat;
	ghost var sequences : seq<seq<T>>;

	constructor(default : T)
		// ensures this.maxPriority == maxPriority
		ensures sequences == emptyLists(maxPriority)
		ensures flatten(sequences) == []
		ensures queues.Length == maxPriority
	{
		// this.maxPriority := maxPriority;
		new;
		this.elements := 0;
		var initializer := new Queue<T>(default);
		this.queues := new Queue<T>[maxPriority]((_) => initializer);
		this.sequences := emptyLists(maxPriority);
		// this.Repr := {this, queues[0], queues[1], queues[2]};
	} 

	predicate Valid()
	{
		&& |sequences| == maxPriority
		&& queues.Length == maxPriority
		&& elements == |flatten(sequences)|
		&& forall i :: 0 <= i < maxPriority ==> queues[i].Valid()
		&& forall i :: 0 <= i < maxPriority ==> sequences[i] == queues[i].elemSeq	
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
		assert !empty();
		assert flatten(sequences) != [];
		assert exists i :: 0 <= i < maxPriority && sequences[i] != [];
		while i < maxPriority
			invariant 0 <= i < maxPriority
			invariant forall j :: 0 <= j < i ==> sequences[j] == []
			invariant exists j :: i <= j < maxPriority && sequences[j] != []
		{
			if (queues[i].size() > 0)
			{
				break;
			}
			i := i + 1;
		}
		min := i;
	}

	method push(value : T, priority : nat)
		requires 0 < priority <= maxPriority
		ensures sequences[index(priority)] == old(sequences[index(priority)]) + [value]
		ensures size() == old(size()) + 1
		ensures forall k :: 0 <= k < |sequences| && k != index(priority)
		==> sequences[k] == old(sequences[k])
	{
		queues[index(priority)].push(value);
		sequences[index(priority)] := sequences[index(priority)] + [value]; 
	}

	method pop() returns (result : T)
		requires !empty()
		ensures result == old(sequences[index(minPriorityFunc())][0])
		ensures sequences[old(index(minPriorityFunc()))] == old(sequences[index(minPriorityFunc())][1..])
		ensures size() == old(size()) - 1
		ensures forall k :: 0 <= k < |sequences| && k != old(index(minPriorityFunc()))
		==> sequences[k] == old(sequences[k])
	{
		var priority := minPriority();
		result := queues[priority].pop();
		sequences[priority] := sequences[priority][1..];
	}
}

method TestPriorityQueue()
{
	var q := new PriorityQueue<int>(0);
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
