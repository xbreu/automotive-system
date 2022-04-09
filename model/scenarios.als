module scenarios

open structure as s

// ----------------------------------------------------------------------------
// Actuators
// ----------------------------------------------------------------------------

one sig Actuators {}

abstract sig DummyActuator {}
lone sig Blink
       , LowBeam
       , CorneringLight
       , TailLamp
       , BrakeLight
       , ReverseLight
       , HighBeam
 extends DummyActuator {}

fact {
  one (s/Blink + this/Blink)
  one (s/LowBeam + this/LowBeam)
  one (s/CorneringLight + this/CorneringLight)
  one (s/TailLamp + this/TailLamp)
  one (s/BrakeLight + this/BrakeLight)
  one (s/ReverseLight + this/ReverseLight)
  one (s/HighBeam + this/HighBeam)
}

fun instance : Actuators -> (Actuator + DummyActuator) {
  Actuators -> (Actuator + DummyActuator)
}

// ----------------------------------------------------------------------------
// Pitman Arm
// ----------------------------------------------------------------------------

fun pitmanArmUpDownPosition : PitmanArm -> PitmanArmUpDownPosition {
  pitmanArmUpDown . pitmanArmUpDownPosition
}

fun pitmanArmUpDownDegree : PitmanArm -> PitmanArmDegree {
  pitmanArmUpDown . pitmanArmDegree
}

fun DisabledPitmanArm : set PitmanArm {
  PitmanArm
  - (pitmanArmForthBack . PitmanArmForthBack)
  - (pitmanArmUpDown . PitmanArmUpDown)
}

fun PitmanArmTop : set PitmanArm {
  this/pitmanArmUpDownPosition . Upward
}

fun PitmanArmDown : set PitmanArm {
  this/pitmanArmUpDownPosition . Downward
}

fun PitmanArmLowDegree : set PitmanArm {
  pitmanArmUpDownDegree . LowDegree
}

fun PitmanArmHighDegree : set PitmanArm {
  pitmanArmUpDownDegree . HighDegree
}

// ----------------------------------------------------------------------------
// Light Rotary Switch
// ----------------------------------------------------------------------------

one abstract sig LightRotary {}
lone sig LightRotaryOff
       , LightRotaryAuto
       , LightRotaryOn
 extends LightRotary {}

fact {
  Vehicle.lightRotarySwitch = Off  => one LightRotaryOff
  Vehicle.lightRotarySwitch = Auto => one LightRotaryAuto
  Vehicle.lightRotarySwitch = On   => one LightRotaryOn
}

// ----------------------------------------------------------------------------
// Hazard and Darkness Switches
// ----------------------------------------------------------------------------

lone sig HazardWarning {}
lone sig DarknessMode {}

fact {
	some Vehicle.hazardWarning 	   => some HazardWarning
	some ArmoredVehicle.darknessMode => some DarknessMode
}

// ----------------------------------------------------------------------------
// User Interface
// ----------------------------------------------------------------------------

one sig UserInterface {}

fun pitmanArm : UserInterface -> PitmanArm {
  UserInterface -> PitmanArm
}

fun lightRotary : UserInterface -> LightRotary {
  UserInterface -> LightRotary
}

fun hazardWarning : UserInterface -> HazardWarning {
  UserInterface -> HazardWarning
}

fun darknessMode : UserInterface -> DarknessMode {
  UserInterface -> DarknessMode
}

// ----------------------------------------------------------------------------
// Scenarios
// ----------------------------------------------------------------------------

	// North America, armored car, darkness mode
run Example1 {
  Vehicle.marketCode = NorthAmerica
  one ArmoredVehicle
  some Vehicle.darknessMode
}

	// EU, Key in ignition on position, Light Auto, pitman arm to downward
run Example2 {
  Vehicle.marketCode = Other
  Vehicle.keyState = KeyInIgnitionOnPosition
  Vehicle.lightRotarySwitch = Auto
  some PitmanArm.pitmanArmUpDown
  PitmanArmUpDown.pitmanArmDegree = LowDegree
}
	// Hazard warning on
run Example3 {
  some Vehicle.hazardWarning
}
