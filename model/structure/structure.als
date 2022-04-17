module structure/structure

open structure/predicates

// ----------------------------------------------------------------------------
// Initial Configuration
// ----------------------------------------------------------------------------

fact init {
  Vehicle . keyState          = NoKeyInserted
  Vehicle . currentSpeed      = Low
  Vehicle . brakePedal        = Low
  Vehicle . voltageBattery    = Medium
  Vehicle . lightRotarySwitch = Off

  some closedDoors
  no pitmanArmForthBack
  no pitmanArmUpDown
  no hazardWarning
  no darknessMode
  no reverseGear
  no oncommingTraffic
  some cameraReady

  no Actuator
  no ActuatorWithLevel
}

// ----------------------------------------------------------------------------
// Properties
// ----------------------------------------------------------------------------

// Control of the low beam headlights. If daytime running light is activated,
// low beam headlights are active all the time and ambient light illuminates
// the vehicle surrounding while leaving the car during darkness. The function
// low beam headlight also includes parking light.
fact daytimeLightsBeams {
  always (
    some daytimeLights => some LowBeamLeft and some LowBeamRight
  )
}

// Direction blinking is only available when the ignition is on.
fact directionDependsOnIgnition {
  always (
    (highBlinkLeft or highBlinkRight)
    => Vehicle . keyState = KeyInIgnitionOnPosition
  )
}

// ----------------------------------------------------------------------------
// Operations
// ----------------------------------------------------------------------------

fact traces {
  always (
    nop or
    some p : PitmanArm | activateBlinkingLeft[p]
                      or activateBlinkingRight[p]
                      or activateTipBlinkingLeft[p]
                      or activateTipBlinkingRight[p]
  )
}

pred nop {

}

pred activateBlinkingLeft[p : PitmanArm] {
  no pitmanArmUpDown

  p . pitmanArmUpDown . pitmanArmUpDownPosition' = Downward
  p . pitmanArmUpDown . pitmanArmDegree' = HighDegree
}

pred disableBlinkingLeft[p : PitmanArm] {
  p . pitmanArmUpDown . pitmanArmUpDownPosition = Downward
  p . pitmanArmUpDown . pitmanArmDegree = HighDegree

  p . pitmanArmUpDown' = none
}

pred activateBlinkingRight[p : PitmanArm] {
  no pitmanArmUpDown

  p . pitmanArmUpDown . pitmanArmUpDownPosition' = Upward
  p . pitmanArmUpDown . pitmanArmDegree' = HighDegree
}

pred disableBlinkingRight[p : PitmanArm] {
  p . pitmanArmUpDown . pitmanArmUpDownPosition = Upward
  p . pitmanArmUpDown . pitmanArmDegree = HighDegree

  p . pitmanArmUpDown' = none
}

pred activateTipBlinkingLeft[p : PitmanArm] {
  no pitmanArmUpDown

  p . pitmanArmUpDown . pitmanArmUpDownPosition' = Downward
  p . pitmanArmUpDown . pitmanArmDegree' = LowDegree
}

pred disableTipBlinkingLeft[p : PitmanArm] {
  p . pitmanArmUpDown . pitmanArmUpDownPosition = Downward
  p . pitmanArmUpDown . pitmanArmDegree = LowDegree

  p . pitmanArmUpDown' = none
}

pred activateTipBlinkingRight[p : PitmanArm] {
  no pitmanArmUpDown

  p . pitmanArmUpDown . pitmanArmUpDownPosition' = Upward
  p . pitmanArmUpDown . pitmanArmDegree' = LowDegree
}

pred disableBlinkingLeft[p : PitmanArm] {
  p . pitmanArmUpDown . pitmanArmUpDownPosition = Upward
  p . pitmanArmUpDown . pitmanArmDegree = LowDegree

  p . pitmanArmUpDown' = none
}
