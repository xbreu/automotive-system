datatype Signal = Brake(nat) // Deflection
	| Reverse(bool) // Activation
	| Voltage(int) // Volt level
	| Beam(nat) // Luminosity

function method getPriority(signal : Signal) : nat
{
	match signal
		case Voltage(_) => 1
		case Brake(_) => 2
		case _ => 3
}
