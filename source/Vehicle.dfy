include "PriorityQueue.dfy"
include "Signal.dfy"

// Vehicle class
class {:autocontracts} Vehicle {
	var queue : PriorityQueue;
	//var lights : array<int>;

	predicate Valid()
	{
		queue.Valid()
	}

	function sequences() : seq<seq<Signal>>
	{
		queue.sequences
	}

	constructor()
		ensures sequences() == emptyLists()
	{
		queue := new PriorityQueue(Reverse(false));
	}

	function method queueSize() : nat
		ensures queueSize() == |flatten(sequences())|
	{
		queue.size()
	}

	predicate method emptyQueue()
		ensures emptyQueue() <==> (queueSize() == 0)
	{
		queue.empty()
	}

	function firstNonEmptyPriority() : nat
		requires !emptyQueue()
		ensures 0 < firstNonEmptyPriority() <= maxPriority
		ensures |sequences()[index(firstNonEmptyPriority())]| > 0
		ensures forall k :: 0 <= k < |sequences()| && sequences()[k] != []
		==> index(firstNonEmptyPriority()) <= k 
	{
		priority(firstNonEmpty(sequences()))
	}
	
	method addSignal(signal : Signal)
		ensures sequences()[index(getPriority(signal))]
		== old(sequences()[index(getPriority(signal))]) + [signal]
		ensures forall k :: 0 <= k < |sequences()| && k != index(getPriority(signal))
		==> sequences()[k] == old(sequences()[k])
		ensures queueSize() == old(queueSize()) + 1
		ensures |sequences()| == maxPriority
	{
		queue.push(signal, getPriority(signal));
	}
	
	method processFirst()
		requires !queue.empty()
		ensures queueSize() == old(queueSize()) - 1
		ensures sequences()[old(index(firstNonEmptyPriority()))] 
			== old(sequences()[index(firstNonEmptyPriority())][1..])
		ensures forall k :: (0 <= k < |sequences()| && k != old(index(firstNonEmptyPriority())))
			==> sequences()[k] == old(sequences()[k])
		{
		// Get the first element from the queue
		var element := queue.pop();

		// Process element
	}

	function method getFirst() : Signal
		requires !emptyQueue()
		ensures getFirst() == sequences()[index(priority(firstNonEmpty(sequences())))][0]
	{
		queue.peek()
	}
}

method TestVehicle()
{
	var v := new Vehicle();

	assert v.sequences() == [[], [], []];

	v.addSignal(Reverse(false));

	assert index(getPriority(Reverse(false))) == 2;
	assert v.sequences()[0] == [];
	assert v.sequences()[1] == [];
	assert v.sequences()[2] == [Reverse(false)];
	assert |v.sequences()| == 3;
	assert v.sequences() == [[], [], [Reverse(false)]];

	v.addSignal(Voltage(30));
	
	assert index(getPriority(Voltage(30))) == 0;
	assert v.sequences()[0] == [Voltage(30)];
	assert v.sequences()[1] == [];
	assert v.sequences()[2] == [Reverse(false)];
	assert |v.sequences()| == 3;
	assert v.sequences() == [[Voltage(30)], [], [Reverse(false)]];

	v.addSignal(Brake(5));

	assert index(getPriority(Brake(5))) == 1;
	assert v.sequences()[0] == [Voltage(30)];
	assert v.sequences()[1] == [Brake(5)];
	assert v.sequences()[2] == [Reverse(false)];
	assert |v.sequences()| == 3;
	assert v.sequences() == [[Voltage(30)], [Brake(5)], [Reverse(false)]];

	var s := v.getFirst();

	assert s == Voltage(30);

	v.processFirst();
	assert v.queueSize() == 2;
	assert v.sequences()[0] == [];
	assert v.sequences()[1] == [Brake(5)];
	assert v.sequences()[2] == [Reverse(false)];
}
