include "PriorityQueue.dfy"
include "Signal.dfy"

// Vehicle class
class {:autocontracts} Vehicle {
	var queue : SignalQueue;

	predicate Valid()
	{
		true
	}

	constructor()
	{
		queue := new SignalQueue();
	}

	method addSignal(signal : Signal)
	{
		queue.add(signal);
	}

	method processFirst()
		requires !queue.empty()
	{
		// Get the first element from the queue
		var element := queue.pop();
	}
}
