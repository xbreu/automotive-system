datatype Signal = Brake(int) // Deflection
	| Reverse(bool) // Activation
	| Voltage(int) // Volt level
	| Beam(int) // Luminosity

// Vehicle class
class {:autocontracts} Vehicle {
	var dummy : nat;
	var dummy2 : nat;
	var queue : seq<Signal>;

	predicate Valid()
	{
		dummy + dummy2 > 0
	}
	
	constructor()
	{
		dummy := 0;
		dummy2 := 1;
	}

	method addSignal(signal : Signal)
		modifies this
	{
		queue := queue + [signal];
	}
	
	method processFirst()
	{
		// Get the first element from the queue
		
	}
}

class {:autocontracts} VehicleFriend {
	constructor()
	{
		
	}

	predicate Valid()
	{
		true
	}
	
	method changeVehicle(vehicle : Vehicle)
		modifies vehicle
		ensures vehicle.dummy == 1
		ensures vehicle.dummy2 == 0
		ensures vehicle.dummy + vehicle.dummy2 > 0
		ensures vehicle.Valid()
	{
		vehicle.dummy2 := 0;
		vehicle.dummy := 1;
	}
}

method Main() {
	var v := new Vehicle();
	print v.dummy, " ", v.dummy2, "\n";
	var f := new VehicleFriend();
	f.changeVehicle(v);
	print v.dummy, " ", v.dummy2, "\n";
}
