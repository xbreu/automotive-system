include "PriorityQueue.dfy"
include "Signal.dfy"

const priorityValues : nat := 3

// Vehicle class
class {:autocontracts} Vehicle {
	// Sensors
	var voltage            : nat; // 0 - 500 dV
	var exteriorBrightness : nat; // 0 – 100000 lx
	// User interface
	var keyStatus          : KeyPosition;
	var lightRotary        : SwitchPosition;
	var reverse            : bool;
	var brake              : nat; // 0 - 450 * 0.1 degrees
	var engineOn           : bool;
	// Actuators
	var lowBeams           : nat; // 0 - 100 %
	var tailLamps          : nat; // 0 - 100 %
	var corneringLights    : nat; // 0 - 100 %
	var brakeLight         : nat; // 0 - 100 %
	var reverseLight       : nat; // 0 - 100 %
	// Implementation attributes
	const queue            : PriorityQueue;

	// --------------------------------------------------------------------------------
	// Constructor and valid predicate
	// --------------------------------------------------------------------------------

	constructor()
		ensures sequences() == emptyLists(priorityValues)
		ensures voltage == 100
		ensures exteriorBrightness == 50000
		ensures keyStatus == NoKeyInserted
		ensures lightRotary == Off
		ensures reverse == false
		ensures brake == 0
		ensures engineOn == false
		ensures lowBeams == 0
		ensures tailLamps == 0
		ensures corneringLights == 0
		ensures brakeLight == 0
		ensures reverseLight == 0
		ensures fresh(queue)
		ensures fresh(queue.queues)
		ensures forall i :: 0 <= i < priorityValues ==> fresh(queue.queues[i])
		ensures forall i :: 0 <= i < priorityValues ==> fresh(queue.queues[i].elements)
	{
		queue := new PriorityQueue(priorityValues, Reverse(false));
		voltage := 100;
		exteriorBrightness := 50000;
		keyStatus := NoKeyInserted;
		lightRotary := Off;
		reverse := false;
		brake := 0;
		engineOn := false;
		lowBeams := 0;
		tailLamps := 0;
		corneringLights := 0;
		brakeLight := 0;
		reverseLight := 0;
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
		&& (engineOn <==> keyStatus == KeyInIgnitionOnPosition)
		// ELS-14 | If the ignition is On and the light rotary switch is in the position On,
		// then low beam headlights are activated.
		&& (engineOn && lightRotary == On ==> lowBeams > 0)
		// ELS-15 | While the ignition is in position KeyInserted: if the light rotary switch
		// is turned to the position On, the low beam headlights are activated
		// with 50% (to save power).
		&& (keyStatus == KeyInserted && lightRotary == On ==> lowBeams == 50)
		// ELS-16 | If the ignition is already off and the driver turns the light rotary
		// switch to position Auto, the low beam headlights remain off or are
		// deactivated (depending on the previous state).
		&& (!engineOn && lightRotary == Auto ==> lowBeams == 0)
		// ELS-18 | If the light rotary switch is in position Auto and the ignition is On, the
		// low beam headlights are activated as soon as the exterior brightness
		// is lower than a threshold of 200 lx. If the exterior brightness exceeds
		// a threshold of 250 lx, the low beam headlights are deactivated.
		&& (engineOn && lightRotary == Auto && exteriorBrightness < 200 ==> lowBeams > 0)
		&& (engineOn && lightRotary == Auto && exteriorBrightness > 250 ==> lowBeams == 0)
		// ELS-22 | Whenever the low or high beam headlights are activated, the tail
		// lights are activated, too.
		&& (lowBeams > 0 ==> tailLamps > 0)
		// ELS-27 | If reverse gear is activated, both opposite cornering lights are
		// activated.
		&& (reverse ==> corneringLights > 0)
		// ELS-29 | The normal brightness of low beam lamps, brake lights, direction
		// indicators, tail lamps, cornering lights, and reverse light is 100%.
		&& (engineOn && lowBeams > 0 ==> lowBeams == 100)
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

	function front() : Signal
		reads this.Repr
		reads queue
		reads queue.queues
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i].elements
		reads set i | 0 <= i < queue.queues.Length :: queue.queues[i]`used
		reads set x, y | y in (set i | 0 <= i < queue.queues.Length :: queue.queues[i].Repr) && x in y :: x
		requires !emptyQueue()
	{
		sequences()[index(firstNonEmptyPriority())][0]
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
		modifies this
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
		ensures match old(front())
		  case Voltage(level) => voltage == level
			case _ => voltage == old(voltage)
		ensures match old(front())
		  case ExteriorBrightness(level) => exteriorBrightness == level
			case _ => exteriorBrightness == old(exteriorBrightness)
		ensures match old(front())
		  case KeyStatus(status) => keyStatus == status
			case _ => keyStatus == old(keyStatus)
		ensures match old(front())
		  case LightRotary(value) => lightRotary == value
			case _ => lightRotary == old(lightRotary)
		ensures match old(front())
		  case Reverse(value) => reverse == value
			case _ => reverse == old(reverse)
		ensures match old(front())
		  case Brake(value) => brake == value
			case _ => brake == old(brake)	
	{	
		// Get the first element from the queue
		var element := queue.pop();
		match element {
			case Voltage(level) => {
				voltage := level;
			}
			case ExteriorBrightness(level) => {
				exteriorBrightness := level;
			}
			case KeyStatus(status) => {
				keyStatus := status;
			}
			case LightRotary(position) => {
				lightRotary := position;
			}
			case Reverse(activation) => {
				reverse := activation;
			}
			case Brake(deflection) => {
				brake := deflection;
			}
		}
	}
}

method TestVehicle()
{
	var v := new Vehicle();
	assert v.sequences() == [[], [], []];
	assert v.keyStatus == NoKeyInserted;
	assert v.voltage == 10;

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
