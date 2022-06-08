include "PriorityQueue.dfy"
include "Signal.dfy"

datatype SwitchPosition = On | Off | Auto
datatype KeyPosition = NoKeyInserted | KeyInserted | KeyInIgnitionOnPosition
	
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
		ensures sequences() == emptyLists()
		ensures keyStatus == NoKeyInserted
		ensures lightRotary == Off
		ensures voltage == 10
		ensures brake == 0
		ensures reverse == false
		ensures frontLights     == 0;
		ensures rearLights      == 0;
		ensures centerRearLight == 0;
		ensures fresh(queue)
	{
		queue           := new PriorityQueue(Reverse(false));
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
	{
		&& queue.Valid()
	}

	// --------------------------------------------------------------------------------
	// Activation predicates
	// --------------------------------------------------------------------------------
	
	predicate method subvoltage()
	{
		voltage <= 8
	}

	predicate method overvoltage()
	{
		voltage >= 15
	}

	predicate ignitionOn()
	{
		keyStatus == KeyInIgnitionOnPosition
	}

	predicate lowBeams()
	{
		|| (ignitionOn() && lightRotary == On)
		|| (ignitionOn() && lightRotary == Auto && exteriorBrightness <= 200)
	}

	predicate powerSaving()
	{
		keyStatus == KeyInserted && lightRotary == On
	}
	
	// --------------------------------------------------------------------------------
	// Attribute functions
	// --------------------------------------------------------------------------------
	
	function sequences() : seq<seq<Signal>>
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
	{
		this.lightRotary := status;
	}

	// --------------------------------------------------------------------------------
	// Queue state
	// --------------------------------------------------------------------------------
	
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

	function method getFirst() : Signal
		requires !emptyQueue()
		ensures getFirst() == sequences()[index(priority(firstNonEmpty(sequences())))][0]
	{
		queue.peek()
	}
	
	method addSignal(signal : Signal)
		ensures sequences()[index(getPriority(signal))]
		== old(sequences()[index(getPriority(signal))]) + [signal]
		ensures forall k :: 0 <= k < |sequences()| && k != index(getPriority(signal))
		==> sequences()[k] == old(sequences()[k])
		ensures queueSize() == old(queueSize()) + 1
		ensures |sequences()| == maxPriority
		ensures queue == old(queue)
	{
		queue.push(signal, getPriority(signal));
	}
	
	// --------------------------------------------------------------------------------
	// Processing
	// --------------------------------------------------------------------------------
	
	method processFirst()
		modifies queue.queue0.elements
		modifies queue.queue0`used
		modifies queue.queue0`elemSeq
		modifies queue.queue1.elements
		modifies queue.queue1`used
		modifies queue.queue1`elemSeq
		modifies queue.queue2.elements
		modifies queue.queue2`used
		modifies queue.queue2`elemSeq
		modifies queue`elements
		modifies queue`sequences
		modifies this`reverse
		modifies this`brake
		modifies this`voltage
		modifies this`rearLights
		modifies this`frontLights
		modifies this`centerRearLight
		requires !queue.empty()
		ensures queue == old(queue)
		ensures queueSize() == old(queueSize()) - 1
		ensures sequences()[old(index(firstNonEmptyPriority()))] 
			== old(sequences()[index(firstNonEmptyPriority())][1..])
		ensures forall k :: (0 <= k < |sequences()| && k != old(index(firstNonEmptyPriority())))
		  ==> sequences()[k] == old(sequences()[k])
		ensures queue == old(queue)
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
				assert this.voltage == level;
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
		ensures this.rearLights == 100
	{
		this.reverse := activation;
		this.rearLights := 100;
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
	{
		this.brake := deflection;
		this.rearLights := 100;
		this.centerRearLight := 100;
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
		modifies queue.queue0.elements
		modifies queue.queue0`used
		modifies queue.queue0`elemSeq
		modifies queue.queue1.elements
		modifies queue.queue1`used
		modifies queue.queue1`elemSeq
		modifies queue.queue2.elements
		modifies queue.queue2`used
		modifies queue.queue2`elemSeq
		modifies queue`elements
		modifies queue`sequences
		modifies this`reverse
		modifies this`brake
		modifies this`voltage
		modifies this`rearLights
		modifies this`frontLights
		modifies this`centerRearLight
		ensures queueSize() == 0
		ensures sequences() == emptyLists()
		ensures queue == old(queue)
	{
		assert queue.Valid();
		assert Valid();
		var oldSize := queueSize();
		var size := oldSize;

		while size > 0
			decreases size
			invariant queue == old(queue)
			invariant 0 <= size <= oldSize
			invariant queue.Valid()
			invariant Valid()
			invariant size == queueSize()
		{
			assert queue.Valid();
			assert Valid();
			processFirst();
			assert queue.Valid();
			assert Valid();
			size := size - 1;
		}

		assert this in Repr;
		assert null !in Repr;
    assert queue in Repr;
		assert queue.Repr <= Repr;
		assert this !in queue.Repr;
		assert queue.Valid();
		assert Valid();
		assert queue == old(queue);
		assert fresh(Repr - old(Repr));
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
