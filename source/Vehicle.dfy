include "PriorityQueue.dfy"
include "Signal.dfy"

lemma flattenEmptyImpliesAllEmpty<T>(sequences : seq<seq<T>>)
  ensures (|flatten(sequences)| == 0) <==>
	  (forall i :: 0 <= i < |sequences| ==> sequences[i] == [])
{
	if (|flatten(sequences)| == 0) {
		assert flatten(sequences) == [];
		if |sequences| == 0 {
			assert forall i :: 0 <= i < |sequences| ==> sequences[i] == [];
		} else {
			assert sequences[0] == [];
			flattenEmptyImpliesAllEmpty(sequences[1..]);
			// assert forall i :: 0 <= i < |sequences| ==> sequences[i] == [];
		}
	}
}

datatype SwitchPosition = On | Off | Auto
datatype KeyPosition = NoKeyInserted | KeyInserted | KeyInIgnitionOnPosition

const priorityValues : nat := 3

// Vehicle class
class {:autocontracts} Vehicle {
	// Primitive attributes
	var keyStatus          : KeyPosition;
	var lightRotary        : SwitchPosition;
	var reverse            : bool;
	var voltage            : int;
	var brake              : nat;
	var frontLights        : nat;
	var rearLights         : nat;
	var centerRearLight    : nat;
	var exteriorBrightness : nat;
	// Implementation attributes
	var queue              : PriorityQueue;

	// --------------------------------------------------------------------------------
	// Constructor and valid predicate
	// --------------------------------------------------------------------------------

	constructor()
		ensures sequences() == emptyLists(priorityValues)
		ensures voltage == 10
		ensures brake == 0
		ensures reverse == false
		ensures fresh(queue)
	{
		queue           := new PriorityQueue(priorityValues, Reverse(false));
		keyStatus       := NoKeyInserted;
		lightRotary     := Off;
		reverse         := false;
		voltage         := 10;
		brake           := 0;
		frontLights     := 0;
		rearLights      := 0;
		centerRearLight := 0;
	}
	
	predicate Valid()
		reads queue
		reads queue.queues
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i].elements
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]`used
		reads set x, y | y in (set i | 0 <= i < queue.queues.Length :: queue.queues[i].Repr) && x in y :: x
	{
		&& queue.Valid()
		&& queue.maxPriority == priorityValues
	}

	// --------------------------------------------------------------------------------
	// Activation predicates
	// --------------------------------------------------------------------------------
	
	predicate subvoltage()
		reads this`voltage
		reads this.Repr
		reads queue
		reads queue.queues
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i].elements
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]`used
		reads set x, y | y in (set i | 0 <= i < queue.queues.Length :: queue.queues[i].Repr) && x in y :: x
	{
		voltage <= 8
	}

	predicate overvoltage()
		reads this`voltage
		reads this.Repr
		reads queue
		reads queue.queues
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i].elements
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]`used
		reads set x, y | y in (set i | 0 <= i < queue.queues.Length :: queue.queues[i].Repr) && x in y :: x
	{
		voltage >= 15
	}

	predicate ignitionOn()
		reads this`keyStatus
		reads this.Repr
		reads queue
		reads queue.queues
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i].elements
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]`used
		reads set x, y | y in (set i | 0 <= i < queue.queues.Length :: queue.queues[i].Repr) && x in y :: x
	{
		keyStatus == KeyInIgnitionOnPosition
	}

	predicate lowBeams()
		reads this`keyStatus
		reads this`lightRotary
		reads this`exteriorBrightness
		reads this.Repr
		reads queue
		reads queue.queues
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i].elements
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]`used
		reads set x, y | y in (set i | 0 <= i < queue.queues.Length :: queue.queues[i].Repr) && x in y :: x
	{
		|| (ignitionOn() && lightRotary == On)
		|| (ignitionOn() && lightRotary == Auto && exteriorBrightness <= 200)
	}

	predicate powerSaving()
		reads this`keyStatus
		reads this`lightRotary
		reads this.Repr
		reads queue
		reads queue.queues
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i].elements
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]`used
		reads set x, y | y in (set i | 0 <= i < queue.queues.Length :: queue.queues[i].Repr) && x in y :: x
	{
		keyStatus == KeyInserted && lightRotary == On
	}
	
	// --------------------------------------------------------------------------------
	// Attribute functions
	// --------------------------------------------------------------------------------
	
	function sequences() : seq<seq<Signal>>
		reads this.Repr
		reads queue
		reads queue.queues
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i].elements
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]`used
		reads set x, y | y in (set i | 0 <= i < queue.queues.Length :: queue.queues[i].Repr) && x in y :: x
	{
		queue.sequences
	}

	// --------------------------------------------------------------------------------
	// Queue state
	// --------------------------------------------------------------------------------
	
	function method queueSize() : nat
		reads this.Repr
		reads queue
		reads queue.queues
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i].elements
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]`used
		reads set x, y | y in (set i | 0 <= i < queue.queues.Length :: queue.queues[i].Repr) && x in y :: x
		ensures queueSize() == |flatten(sequences())|
	{
		queue.size()
	}

	predicate method emptyQueue()
		reads this.Repr
		reads queue
		reads queue.queues
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i].elements
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]`used
		reads set x, y | y in (set i | 0 <= i < queue.queues.Length :: queue.queues[i].Repr) && x in y :: x
		ensures emptyQueue() <==> (queueSize() == 0)
	{
		queue.empty()
	}

	function firstNonEmptyPriority() : nat
		reads this.Repr
		reads queue
		reads queue.queues
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i].elements
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]`used
		reads set x, y | y in (set i | 0 <= i < queue.queues.Length :: queue.queues[i].Repr) && x in y :: x
		requires !emptyQueue()
		ensures 0 < firstNonEmptyPriority() <= priorityValues
		ensures |sequences()[index(firstNonEmptyPriority())]| > 0
		ensures forall k :: 0 <= k < |sequences()| && sequences()[k] != []
		==> index(firstNonEmptyPriority()) <= k 
	{
		priority(firstNonEmpty(sequences()))
	}

	method getFirst() returns (result : Signal)
		requires !emptyQueue()
		ensures !emptyQueue()
		ensures result == sequences()[index(firstNonEmptyPriority())][0]
		ensures queue == old(queue)
		ensures queue.elements == old(queue.elements)
		ensures queue.sequences == old(queue.sequences)
		ensures result == queue.sequences[index(queue.minPriorityFunc())][0]
		ensures forall i :: 0 <= i < queue.queues.Length
		  ==> queue.queues[i] == old(queue.queues[i])
		ensures forall i :: 0 <= i < queue.queues.Length
		  ==> queue.queues[i].elements == old(queue.queues[i].elements)
		ensures queue.Repr == old(queue.Repr)
	{
		result := queue.peek();
	}
	
	method addSignal(signal : Signal)
		modifies queue
		modifies queue.queues
		modifies queue`elements
		modifies queue`sequences
		modifies set i | 0 <= i < queue.queues.Length :: queue.queues[i]
		modifies set i | 0 <= i < queue.queues.Length :: queue.queues[i].elements
		ensures sequences()[index(getPriority(signal))]
		  == old(sequences()[index(getPriority(signal))]) + [signal]
		ensures forall k :: 0 <= k < |sequences()| && k != index(getPriority(signal))
		  ==> sequences()[k] == old(sequences()[k])
		ensures queueSize() == old(queueSize()) + 1
		ensures |sequences()| == priorityValues
		ensures queue == old(queue)
	{
		queue.push(signal, getPriority(signal));
	}
	
	// --------------------------------------------------------------------------------
	// Processing
	// --------------------------------------------------------------------------------
	
	method processFirst()
		modifies this`reverse
		modifies this`brake
		modifies this`voltage
		modifies queue
		modifies queue.queues
		modifies set i | 0 <= i < queue.queues.Length :: queue.queues[i]
		modifies set i | 0 <= i < queue.queues.Length :: queue.queues[i].elements
		modifies queue`elements
		modifies queue`sequences
		requires !queue.empty()
		ensures sequences()[old(index(firstNonEmptyPriority()))] == old(sequences()[index(firstNonEmptyPriority())][1..])
		ensures queueSize() == old(queueSize()) - 1
		ensures forall k :: 0 <= k < |sequences()| && k != old(index(firstNonEmptyPriority()))
		  ==> sequences()[k] == old(sequences()[k])
		ensures queue.Repr == old(queue.Repr)
		ensures forall i :: 0 <= i < queue.queues.Length
		  ==> queue.queues[i] == old(queue.queues[i])
		ensures forall i :: 0 <= i < queue.queues.Length
		  ==> queue.queues[i].elements == old(queue.queues[i].elements)
		ensures queue == old(queue)
		ensures queue.queues == old(queue.queues)
		{
		// Get the first element from the queue
		var element := queue.pop();

		// Process element
		match element
			case Reverse(activation) => { this.reverse := activation; }
			case Beam(level) => {}
			case Brake(deflection) => { this.brake := deflection; }
			case Voltage(level) => { this.voltage := level; }

	}

	method processAll()
		modifies this`reverse
		modifies this`brake
		modifies this`voltage
		modifies queue
		modifies queue.queues
		modifies set i | 0 <= i < queue.queues.Length :: queue.queues[i]
		modifies set i | 0 <= i < queue.queues.Length :: queue.queues[i].elements
		modifies queue`elements
		modifies queue`sequences
		ensures queueSize() == 0
		ensures sequences() == emptyLists(priorityValues)
		ensures queue == old(queue)
	{
		// assert queue.Valid();
		// assert Valid();
		var oldSize := queueSize();
		var size := oldSize;

		while size > 0
			decreases size
			invariant queue == old(queue)
			invariant queue.queues == old(queue.queues)
			invariant queue.Repr == old(queue.Repr)
			invariant forall i :: 0 <= i < queue.queues.Length
		    ==> queue.queues[i] == old(queue.queues[i])
			invariant forall i :: 0 <= i < queue.queues.Length
		    ==> queue.queues[i].elements == old(queue.queues[i].elements)
			invariant 0 <= size <= oldSize
			invariant queue.Valid()
			invariant Valid()
			invariant size == queueSize()
		{
			// assert queue.Valid();
			// assert Valid();
			processFirst();
			// assert queue.Valid();
			// assert Valid();
			size := size - 1;
		}

		// assert this in Repr;
		// assert null !in Repr;
    // assert queue in Repr;
		// assert queue.Repr <= Repr;
		// assert this !in queue.Repr;
		// assert queue.Valid();
		// assert Valid();
		// assert queue == old(queue);
		// assert fresh(Repr - old(Repr));
		// assert size == 0;
		// assert |sequences()| == priorityValues;
		// assert |flatten(sequences())| == 0;
		flattenEmptyImpliesAllEmpty(sequences());
		// assert forall i :: 0 <= i < |sequences()| ==> sequences()[i] == [];
		// assert sequences() == emptyLists(priorityValues);
	}
}

method TestVehicle()
{
	var v := new Vehicle();

	assert v.sequences() == [[], [], []];
	assert v.voltage == 10;

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

	v.processFirst();
	assert v.queueSize() == 1;
	assert v.sequences()[0] == [];
	assert v.sequences()[1] == [];
	assert v.sequences()[2] == [Reverse(false)];
}
