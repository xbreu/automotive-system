include "PriorityQueue.dfy"
include "Signal.dfy"

// Vehicle class
class {:autocontracts} Vehicle {
	var queue : PriorityQueue;

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

	method addSignal(signal : Signal)
		ensures sequences()[index(getPriority(signal))]
		== old(sequences()[index(getPriority(signal))]) + [signal]
		ensures forall k :: 0 <= k < |sequences()| && k != index(getPriority(signal))
		==> sequences()[k] == old(sequences()[k])
		ensures queueSize() == old(queueSize()) + 1
	{
		queue.push(signal, getPriority(signal));
	}
	
	method processFirst()
		requires !queue.empty()		
	{
		// Get the first element from the queue
		var element := queue.pop();
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
	assert v.sequences() == [[], [], [Reverse(false)]];
	v.addSignal(Voltage(30));
	v.addSignal(Brake(5));
	assert v.getFirst() == Voltage(30);
}
