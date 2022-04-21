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
  some ArmoredVehicle
  some DarknessModeVehicle
}

// EU, Key in ignition on position, Light Auto, pitman arm to downward
run Example2 {
  no ArmoredVehicle
  no NorthAmericanVehicle
  eventually Vehicle . keyState = KeyInIgnitionOnPosition
  eventually Vehicle . lightRotarySwitch = Auto
  eventually PitmanArmUpDown . pitmanArmUpDownPosition = Downward
  eventually PitmanArmUpDown . pitmanArmDegree = HighDegree
}

// Hazard warning on
run Example3 {
  eventually some HazardWarningVehicle
}

// Direction indicator on, low speed
run Example4 {
  no Actuator
  no BlinkRight
  eventually some BlinkLeft
  Vehicle . currentSpeed = Low
}

// Parking light active
run Example5 {
  parkingLight
}

run TestExample {
  eventually Vehicle . brakePedal = High
}
