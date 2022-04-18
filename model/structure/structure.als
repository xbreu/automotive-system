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
  no PitmanArmUpDown
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

fact fairness {
  always eventually blinkCycle // Change this
}

fact traces {
  always (
    nop
    or blinkCycle
    or activateBlinkingLeft
  )
}

pred nop {
  PitmanArmUpDown' = PitmanArmUpDown
  Actuator' = Actuator
  ActuatorWithLevel' = ActuatorWithLevel
}

pred blinkCycle {
  some BlinkLeft => (
    (some BlinkLeft . level => after no BlinkLeft . level)
    and
    (no BlinkLeft . level => after some BlinkLeft . level)
    and
    after some BlinkLeft
  )

  some BlinkRight => (
    (some BlinkRight . level => after no BlinkRight . level)
    and
    (no BlinkRight . level => after some BlinkRight . level)
    and
    after some BlinkRight
  )
  
  PitmanArmUpDown' = PitmanArmUpDown
}

pred activateBlinkingLeft {
  no PitmanArmUpDown

  some PitmanArm . pitmanArmUpDown'
  after PitmanArmUpDown . pitmanArmUpDownPosition = Downward
  after PitmanArmUpDown . pitmanArmDegree = HighDegree
  after BlinkLeft . level = High
}

run {
  eventually (some BlinkLeft . level)
}

