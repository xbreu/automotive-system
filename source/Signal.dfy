include "PriorityQueue.dfy"

datatype Signal = Brake(int) // Deflection
	| Reverse(bool) // Activation
	| Voltage(int) // Volt level
	| Beam(int) // Luminosity

class {:autocontracts} SignalQueue {
	var queue : PriorityQueue<Signal>;

	constructor()
	{
		queue := new PriorityQueue<Signal>();
	}

	function method getPriority(signal : Signal) : nat
	{
		match signal
			case Voltage(_) => 0
			case _ => 1
	}

	function method size() : nat
	{
		queue.size()
	}

	predicate method empty()
	{
		queue.empty()
	}

	method add(signal : Signal)
	{
		queue.add(getPriority(signal), signal);
	}

	method pop() returns (x : Signal)
		requires !queue.empty()
	{
		x := queue.pop();
	}

	method peek() returns (x : Signal)
		requires !queue.empty()
	{
		x := queue.peek();
	}
}
