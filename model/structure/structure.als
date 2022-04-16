module structure/structure

open structure/signatures

// ----------------------------------------------------------------------------
// Properties
// ----------------------------------------------------------------------------

// Control of the low beam headlights. If daytime running light is activated,
// low beam headlights are active all the time and ambient light illuminates
// the vehicle surrounding while leaving the car during darkness. The function
// low beam headlight also includes parking light.
fact daytimeLightsBeams {
  some daytimeLights => some LowBeamLeft and some LowBeamRight
}

// Direction blinking is only available when the ignition is on.
fact directionDependsOnIgnition {
  (highBlinkLeft or highBlinkRight)
  => Vehicle . keyState = KeyInIgnitionOnPosition
}

// ----------------------------------------------------------------------------
// Operations
// ----------------------------------------------------------------------------

fact Traces {
  always (
    nop or
    some p:PitmanArm | activateBlinkingLeft [p] or
    some p:PitmanArm | activateBlinkingRight [p] or
    some p:PitmanArm | activateTipBlinkingLeft [p] or
    some p:PitmanArm | activateTipBlinkingRight [p]
  )
}

pred nop {

}

pred activateBlinkingLeft [p : PitmanArm] {
  no pitmanArmUpDown

  p . pitmanArmUpDown . pitmanArmUpDownPosition' = Downward
  p . pitmanArmUpDown . pitmanArmDegree' = HighDegree
}

pred activateBlinkingRight [p : PitmanArm] {
  no pitmanArmUpDown

  p . pitmanArmUpDown . pitmanArmUpDownPosition' = Upward
  p . pitmanArmUpDown . pitmanArmDegree' = HighDegree
}

pred activateTipBlinkingLeft [p : PitmanArm] {
  no pitmanArmUpDown

  p . pitmanArmUpDown . pitmanArmUpDownPosition' = Downward
  p . pitmanArmUpDown . pitmanArmDegree' = LowDegree
}

pred activateTipBlinkingRight [p : PitmanArm] {
  no pitmanArmUpDown

  p . pitmanArmUpDown . pitmanArmUpDownPosition' = Downward
  p . pitmanArmUpDown . pitmanArmDegree' = LowDegree
}
