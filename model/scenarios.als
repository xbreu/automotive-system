module scenarios

open structure as s
open visualization as v

// ----------------------------------------------------------------------------
// Auxiliar Relations
// ----------------------------------------------------------------------------

fun instance : Actuators -> (Actuator + DummyActuator) {
  Actuators -> (Actuator + DummyActuator)
}

fun component : UserInterface -> (PitmanArm + DummySwitch) {
  UserInterface -> (PitmanArm + DummySwitch)
}

// ----------------------------------------------------------------------------
// Scenarios
// ----------------------------------------------------------------------------

// North America, armored car, darkness mode
run Example1 {
  Vehicle . marketCode = NorthAmerica
  one ArmoredVehicle
  some Vehicle . darknessMode
}

// EU, Key in ignition on position, Light Auto, pitman arm to downward
run Example2 {
  no ArmoredVehicle
  Vehicle . marketCode = Other
  Vehicle . keyState = KeyInIgnitionOnPosition
  Vehicle . lightRotarySwitch = Auto
  some PitmanArm . pitmanArmUpDown
  PitmanArmUpDown . pitmanArmDegree = LowDegree
}

// Hazard warning on
run Example3 {
  some Vehicle . hazardWarning
}

// Direction indicator on, low speed
run Example4 {
  no Actuator and no BlinkRight and some BlinkLeft
  Vehicle . currentSpeed = Low
}

// Parking light active
run Example5 {
  parkingLight
}
