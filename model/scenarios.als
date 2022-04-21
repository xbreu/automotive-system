module scenarios

open visualization

// ----------------------------------------------------------------------------
// Auxiliar Relations
// ----------------------------------------------------------------------------

one sig Actuators {}
fun instance : Actuators -> (Actuator + ActuatorWithLevel) {
  Actuators -> (Actuator + ActuatorWithLevel)
}

one sig UserInterface {}
fun component : UserInterface -> PitmanArm {
  UserInterface -> PitmanArm
}

// ----------------------------------------------------------------------------
// Scenarios
// ----------------------------------------------------------------------------

run FreeExample {}

// North America, armored car, darkness mode
run Example1 {
  some NorthAmericanVehicle
  one ArmoredVehicle
  some DarknessModeVehicle
}

// EU, Key in ignition on position, Light Auto, pitman arm to downward
run Example2 {
  no ArmoredVehicle
  no NorthAmericanVehicle
  Vehicle . keyState = KeyInIgnitionOnPosition
  Vehicle . lightRotarySwitch = Auto
  PitmanArmUpDown . pitmanArmUpDownPosition = Downward
  PitmanArmUpDown . pitmanArmDegree = HighDegree
}

// Hazard warning on
run Example3 {
  some HazardWarningVehicle
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
