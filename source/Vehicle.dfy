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
		ensures voltage == 10
		ensures brake == 0
		ensures reverse == false
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
	
	predicate subvoltage()
	{
		voltage <= 8
	}

	predicate overvoltage()
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
			case Reverse(activation) => { this.reverse := activation; }
			case Beam(level) => {}
			case Brake(deflection) => { this.brake := deflection; }
			case Voltage(level) => 
				{ 
					executeVoltage(level); 
					assert voltage == level;
				}

	}

	method executeVoltage(level : int)
		modifies this`voltage
		ensures queue.queue0.elements == old(queue.queue0.elements)
		ensures queue.queue0.used == old(queue.queue0.used)
		ensures queue.queue0.elemSeq == old(queue.queue0.elemSeq)
		ensures queue.queue1.elements == old(queue.queue1.elements)
		ensures queue.queue1.used == old(queue.queue1.used)
		ensures queue.queue1.elemSeq == old(queue.queue1.elemSeq)
		ensures queue.queue2.elements == old(queue.queue2.elements)
		ensures queue.queue2.used == old(queue.queue2.used)
		ensures queue.queue2.elemSeq == old(queue.queue2.elemSeq)
		ensures queue.elements == old(queue.elements)
		ensures queue.sequences == old(queue.sequences)
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
	assert v.voltage == 30;
	assert v.queueSize() == 2;
	assert v.sequences()[0] == [];
	assert v.sequences()[1] == [Brake(5)];
	assert v.sequences()[2] == [Reverse(false)];

	v.processFirst();
	assert v.queueSize() == 1;
	assert v.sequences()[0] == [];
	assert v.sequences()[1] == [];
	assert v.sequences()[2] == [Reverse(false)];

	v.processAll();
	assert v.queueSize() == 0;
}
