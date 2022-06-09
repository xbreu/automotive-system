include "PriorityQueue.dfy"
include "Signal.dfy"

const priorityValues : nat := 3

// Vehicle class
class {:autocontracts} Vehicle {
	// User interface
	var keyStatus          : KeyPosition;
	var ignitionOn         : bool;
	var lightRotary        : SwitchPosition;
	var reverse            : bool;
	var brake              : nat; // 0 - 450 * 0.1 degrees
	// Actuators
	var lowBeams           : nat; // 0 - 100 %
	var tailLamps          : nat; // 0 - 100 %
	var corneringLights    : nat; // 0 - 100 %
	var brakeLight         : nat; // 0 - 100 %
	var reverseLight       : nat; // 0 - 100 %
	// Sensors
	var voltage            : nat; // 0 - 500 dV
	var exteriorBrightness : nat; // 0 – 100000 lx
	// Concrete state of the lights
	var frontLights        : nat;
	var rearLights         : nat;
	var centerRearLight    : nat;
	// Implementation attributes
	const queue            : PriorityQueue;

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
		ensures frontLights     == 0
		ensures rearLights      == 0
		ensures centerRearLight == 0
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
		// Variable domains
		&& (brake <= 450)
		&& (lowBeams <= 100)
		&& (tailLamps <= 100)
		&& (corneringLights <= 100)
		&& (brakeLight <= 100)
		&& (reverseLight <= 100)
		&& (exteriorBrightness <= 100000)
		// Dependant variables
		&& (ignitionOn <==> keyStatus == KeyInIgnitionOnPosition)
		// ELS-14 | If the ignition is On and the light rotary switch is in the position On,
		// then low beam headlights are activated.
		&& (ignitionOn && lightRotary == On ==> lowBeams > 0)
		// ELS-15 | While the ignition is in position KeyInserted: if the light rotary switch
		// is turned to the position On, the low beam headlights are activated
		// with 50% (to save power).
		&& (keyStatus == KeyInserted && lightRotary == On ==> lowBeams == 50)
		// ELS-16 | If the ignition is already off and the driver turns the light rotary
		// switch to position Auto, the low beam headlights remain off or are
		// deactivated (depending on the previous state).
		&& (!ignitionOn && lightRotary == Auto ==> lowBeams == 0)
		// ELS-18 | If the light rotary switch is in position Auto and the ignition is On, the
		// low beam headlights are activated as soon as the exterior brightness
		// is lower than a threshold of 200 lx. If the exterior brightness exceeds
		// a threshold of 250 lx, the low beam headlights are deactivated.
		&& (ignitionOn && lightRotary == Auto && exteriorBrightness < 200 ==> lowBeams > 0)
		&& (ignitionOn && lightRotary == Auto && exteriorBrightness > 250 ==> lowBeams == 0)
		// ELS-22 | Whenever the low or high beam headlights are activated, the tail
		// lights are activated, too.
		&& (lowBeams > 0 ==> tailLamps > 0)
		// ELS-27 | If reverse gear is activated, both opposite cornering lights are
		// activated.
		&& (reverse ==> corneringLights > 0)
		// ELS-29 | The normal brightness of low beam lamps, brake lights, direction
		// indicators, tail lamps, cornering lights, and reverse light is 100%.
		&& (ignitionOn && lowBeams > 0 ==> lowBeams == 100)
		&& (brakeLight > 0 ==> brakeLight == 100)
		&& (tailLamps > 0 ==> tailLamps == 100)
		&& (voltage > 80 && corneringLights > 0 ==> corneringLights == 100)
		&& (reverseLight > 0 ==> reverseLight == 100)
		// ELS-39 | If the brake pedal is deflected more than 3 degrees, all brake lamps have to
		// be activated until the deflection is lower than 1 degree again.
		&& (brake > 30 ==> brakeLight > 0)
		&& (brake < 10 ==> brakeLight == 0)
		// ELS-41 | The reverse light is activated whenever the reverse gear is engaged.
		&& (reverse ==> reverseLight > 0)
		// ELS-45 | With subvoltage the cornering light is not available.
		&& (voltage <= 80 ==> corneringLights == 0)
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
		ensures this.lightRotary == old(this.lightRotary)
		ensures this.voltage == old(this.voltage)
		ensures this.reverse == old(this.reverse)
		ensures this.brake == old(this.brake)
		ensures queueSize() == old(queueSize())
		ensures sequences() == old(sequences())
		ensures queue.elements == old(queue.elements)
		ensures queue.sequences == old(queue.sequences)
		ensures forall i :: 0 <= i < queue.queues.Length
		  ==> queue.queues[i] == old(queue.queues[i])
		ensures forall i :: 0 <= i < queue.queues.Length
		  ==> queue.queues[i].elements == old(queue.queues[i].elements)
		ensures queue.Repr == old(queue.Repr)
	{
		this.keyStatus := status;
		this.ignitionOn := status == KeyInIgnitionOnPosition;
	}

	method changeLightRotary(status : SwitchPosition)
		ensures this.keyStatus == old(this.keyStatus)
		ensures this.lightRotary == status
		ensures this.voltage == old(this.voltage)
		ensures this.reverse == old(this.reverse)
		ensures this.brake == old(this.brake)
		ensures queueSize() == old(queueSize())
		ensures sequences() == old(sequences())
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
		ensures this.voltage == level
		ensures sequences() == old(sequences())
	{
		this.voltage := level;
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
}
