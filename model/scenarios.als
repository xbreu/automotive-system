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
// User Interface
// ----------------------------------------------------------------------------

one sig UserInterface {}

fun pitmanArm : UserInterface -> PitmanArm {
  UserInterface -> PitmanArm
}

// ----------------------------------------------------------------------------
// Scenarios
// ----------------------------------------------------------------------------

	// North America, armored car, darkness mode
run Example1 {
 one ArmoredVehicle
 Vehicle.marketCode = NorthAmerica
 some Vehicle.darknessMode
}

	//  
run Example2 {

}
