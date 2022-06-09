datatype SwitchPosition = On | Off | Auto
datatype KeyPosition = NoKeyInserted | KeyInserted | KeyInIgnitionOnPosition

datatype Signal = Brake(nat)
	| Reverse(bool)
	| Voltage(nat)
	| Beam(nat)
	| ExteriorBrightness(nat)
	| KeyStatus(KeyPosition)
	| LightRotary(SwitchPosition)

function method getPriority(signal : Signal) : nat
{
	match signal
		case Voltage(_) => 1
		case Brake(_) => 2
		case KeyStatus(_) => 2
		case _ => 3
}
