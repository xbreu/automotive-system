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
