datatype Signal = Brake(int) // Deflection
	| Reverse(bool) // Activation
	| Voltage(int) // Volt level
	| Beam(int) // Luminosity

function method getPriority(signal : Signal) : nat
{
	match signal
		case Voltage(_) => 1
		case Brake(_) => 2
		case _ => 3
}
