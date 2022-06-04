//include "Vehicle.dfy"

datatype Signal = Brake(deflection: nat) // Deflection
	| Reverse(active: bool) // Activation
	| Voltage(level: int) // Volt level
	| Beam(luminosity: nat) // Luminosity

function method getPriority(signal : Signal) : nat
{
	match signal
		case Voltage(_) => 1
		case Brake(_) => 2
		case _ => 3
}

/*
trait Signal {
	var priority: nat;
	var vehicle : Vehicle;

	function method getPriority() : nat
	reads this
	{
		priority
	}

	method execute()
	modifies this.vehicle
	modifies this.vehicle.lights
	requires vehicle.lights.Length == 5
} 

class Brake extends Signal {
	var deflection : nat

	constructor (vehicle : Vehicle, deflection : nat)
	ensures this.vehicle == vehicle
	ensures this.priority == 2
	ensures this.deflection == deflection
	{
		this.priority := 2;
		this.vehicle := vehicle;
		this.deflection := deflection;
	}

	method execute()
	modifies this.vehicle
	ensures vehicle.queue  == old(vehicle.queue)
	ensures vehicle.lights  == old(vehicle.lights)
	ensures vehicle.voltage == old(vehicle.voltage)
	ensures vehicle.reverse == old(vehicle.reverse)
	ensures vehicle.brake == deflection
	{
      vehicle.brake := deflection;
	}
}

class Reverse extends Signal {
	var active : bool
	
	constructor (vehicle : Vehicle, active : bool)
	ensures this.vehicle == vehicle
	ensures this.active == active
	ensures this.priority == 3
	{
		this.priority := 3;
		this.vehicle := vehicle;
		this.active := active;
	}

	method execute()
	modifies this.vehicle
	ensures vehicle.queue   == old(vehicle.queue)
	ensures vehicle.lights  == old(vehicle.lights)
	ensures vehicle.voltage == old(vehicle.voltage)
	ensures vehicle.reverse == active
	ensures vehicle.brake   == old(vehicle.brake)
	{
      vehicle.reverse := active;
	}
}

class Beam extends Signal {
	var luminosity : nat
	
	constructor (vehicle : Vehicle, luminosity : nat)
	ensures this.vehicle == vehicle
	ensures this.luminosity == luminosity
	ensures this.priority == 3
	{
		this.priority := 3;
		this.vehicle := vehicle;
		this.luminosity := luminosity;
	}

	method execute()
	modifies this.vehicle.lights
	requires vehicle.lights.Length == 5
	ensures vehicle.lights[0] == luminosity
	ensures vehicle.lights[1] == luminosity
	ensures vehicle.queue   == old(vehicle.queue)
	ensures vehicle.voltage == old(vehicle.voltage)
	ensures vehicle.reverse == old(vehicle.reverse)
	ensures vehicle.brake   == old(vehicle.brake)
	{
    	vehicle.lights[0] := luminosity;
		vehicle.lights[1] := luminosity;
	}
}

class Voltage extends Signal {
	var level: int
	
	constructor (vehicle : Vehicle, level : int)
	ensures this.vehicle == vehicle
	ensures this.level == level
	ensures this.priority == 1
	{
		this.priority := 1;
		this.vehicle := vehicle;
		this.level := level;
	}

	method execute()
	modifies this.vehicle
	ensures vehicle.queue   == old(vehicle.queue)
	ensures vehicle.lights  == old(vehicle.lights)
	ensures vehicle.voltage == level
	ensures vehicle.reverse == old(vehicle.reverse)
	ensures vehicle.brake   == old(vehicle.brake)
	{
      vehicle.voltage := level;
	}
}

method TestSignal() {
	var v := new Vehicle();

	assert v.brake == 0;
	
	var brake := new Brake(v, 10);
	brake.execute();
	
	assert v.brake == 10;
	
	var reverse := new Reverse(v, true);
	reverse.execute();

	assert v.reverse == true;

	var voltage := new Voltage(v, 5);
	voltage.execute();

	assert v.voltage == 5;
}
*/