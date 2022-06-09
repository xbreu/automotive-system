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
		ensures keyStatus == NoKeyInserted
		ensures lightRotary == Off
		ensures voltage == 10
		ensures brake == 0
		ensures reverse == false
		ensures frontLights     == 0;
		ensures rearLights      == 0;
		ensures centerRearLight == 0;
		ensures fresh(queue)
		ensures fresh(queue.queues)
		ensures forall i :: 0 <= i < priorityValues ==> fresh(queue.queues[i])
		ensures forall i :: 0 <= i < priorityValues ==> fresh(queue.queues[i].elements)
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
	
	predicate method subvoltage()
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

	predicate method overvoltage()
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
	// 
	// --------------------------------------------------------------------------------

	method changeKeyStatus(status : KeyPosition)
		ensures this.keyStatus == status
		ensures queue.elements == old(queue.elements)
		ensures queue.sequences == old(queue.sequences)
		ensures this.brake == old(this.brake)
		ensures this.voltage == old(this.voltage)
		ensures queueSize() == old(queueSize())
		ensures sequences() == old(sequences())
		ensures queue == old(queue)
		ensures queue.elements == old(queue.elements)
		ensures queue.sequences == old(queue.sequences)
		ensures forall i :: 0 <= i < queue.queues.Length
		  ==> queue.queues[i] == old(queue.queues[i])
		ensures forall i :: 0 <= i < queue.queues.Length
		  ==> queue.queues[i].elements == old(queue.queues[i].elements)
		ensures queue.Repr == old(queue.Repr)
	{
		this.keyStatus := status;
	}

	method changeLightRotary(status : SwitchPosition)
		ensures this.lightRotary == status
		ensures queue.elements == old(queue.elements)
		ensures queue.sequences == old(queue.sequences)
		ensures this.brake == old(this.brake)
		ensures this.voltage == old(this.voltage)
		ensures queueSize() == old(queueSize())
		ensures sequences() == old(sequences())
		ensures queue == old(queue)
		ensures queue.elements == old(queue.elements)
		ensures queue.sequences == old(queue.sequences)
		ensures forall i :: 0 <= i < queue.queues.Length
		  ==> queue.queues[i] == old(queue.queues[i])
		ensures forall i :: 0 <= i < queue.queues.Length
		  ==> queue.queues[i].elements == old(queue.queues[i].elements)
		ensures queue.Repr == old(queue.Repr)
	{
		this.lightRotary := status;
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
		ensures queue.queues == old(queue.queues)
		ensures forall i :: 0 <= i < queue.queues.Length
		  ==> queue.queues[i] == old(queue.queues[i])
		ensures forall i :: 0 <= i < queue.queues.Length
		  ==> queue.queues[i].elements == old(queue.queues[i].elements)
		  || fresh(queue.queues[i].elements)
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
		modifies this`rearLights
		modifies this`frontLights
		modifies this`centerRearLight
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
		ensures match old(sequences()[index(firstNonEmptyPriority())][0])
		  case Reverse(activation) => this.reverse == activation
		  case Brake(deflection) => this.brake == deflection
			case Voltage(level) => this.voltage == level
			case _ => true
	{
		// Get the first element from the queue
		var element := queue.pop();

		// Process element
		match element
			case Reverse(activation) => 
			{ 
				executeReverse(activation);
			}
			case Beam(luminosity) => 
			{
				executeBeam(luminosity);
			}
			case Brake(deflection) => 
			{
				executeBrake(deflection);
			}
			case Voltage(level) => 
			{ 
				executeVoltage(level);
				// assert this.voltage == level;
			}
	}

	method executeReverse(activation : bool)
		modifies this`reverse
		modifies this`rearLights
		ensures queue.elements == old(queue.elements)
		ensures queue.sequences == old(queue.sequences)
		ensures this.brake == old(this.brake)
		ensures this.voltage == old(this.voltage)
		ensures queueSize() == old(queueSize())
		ensures sequences() == old(sequences())
		ensures queue == old(queue)
		ensures this.reverse == activation
		ensures activation && !subvoltage() ==> this.rearLights == 100
		ensures !activation ==> this.rearLights == 0
	{
		this.reverse := activation;
		if activation && !subvoltage()
		{
			this.rearLights := 100;
		}
		else
		{
			this.rearLights := 0;
		}
	}

	method executeBeam(luminosity : nat)
		modifies this`frontLights
		ensures queue.elements == old(queue.elements)
		ensures queue.sequences == old(queue.sequences)
		ensures this.brake == old(this.brake)
		ensures this.voltage == old(this.voltage)
		ensures this.reverse == old(this.reverse)
		ensures this.rearLights == old(this.rearLights)
		ensures queueSize() == old(queueSize())
		ensures sequences() == old(sequences())
		ensures queue == old(queue)
		ensures !subvoltage() && !overvoltage() ==> this.frontLights == luminosity
		ensures overvoltage() ==> this.frontLights == (100 - (this.voltage - 14) * 20) % 100
	{
		if !subvoltage()
		{
			if overvoltage()
			{
				this.frontLights := (100 - (this.voltage - 14) * 20) % 100;
			}
			else
			{
				this.frontLights := luminosity;
			}
		}
	}

	method executeBrake(deflection : nat)
		modifies this`brake
		modifies this`rearLights
		modifies this`centerRearLight
		ensures this.reverse == old(this.reverse)
		ensures this.voltage == old(this.voltage)
		ensures queueSize() == old(queueSize())
		ensures queue == old(queue)
		ensures sequences() == old(sequences())
		ensures this.brake == deflection
		ensures this.brake > 0 ==> (this.rearLights == 100 && this.rearLights == 100)
		ensures this.brake == 0 ==> (this.rearLights == 0 && this.rearLights == 0)
	{
		this.brake := deflection;

		if this.brake > 0
		{
			this.rearLights := 100;
			this.centerRearLight := 100;
		}
		else
		{
			this.rearLights := 0;
			this.centerRearLight := 0;
		}
	}

	method executeVoltage(level : int)
		modifies this`voltage
		ensures this.reverse == old(this.reverse)
		ensures this.brake == old(this.brake)
		ensures queueSize() == old(queueSize())
		ensures queue == old(queue)
		ensures this.voltage == level
		ensures sequences() == old(sequences())
	{
		this.voltage := level;
	}

	method processAll()
		modifies this`reverse
		modifies this`brake
		modifies this`voltage
		modifies this`rearLights
		modifies this`frontLights
		modifies this`centerRearLight
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
	assert v.keyStatus == NoKeyInserted;
	assert v.voltage == 10;

	v.changeKeyStatus(KeyInserted);
	assert v.keyStatus == KeyInserted;

	v.changeLightRotary(On);
	assert v.lightRotary == On;

	// Test add signal

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

	// Test get first
	var s := v.getFirst();
	assert s == Voltage(30);

	// Test process
	v.processFirst();
	assert v.queueSize() == 2;
	assert v.sequences()[0] == [];
	assert v.sequences()[1] == [Brake(5)];
	assert v.sequences()[2] == [Reverse(false)];
	assert v.voltage == 30;

	v.processFirst();
	assert v.queueSize() == 1;
	assert v.sequences()[0] == [];
	assert v.sequences()[1] == [];
	assert v.sequences()[2] == [Reverse(false)];

	v.processAll();
	assert v.queueSize() == 0;
}
