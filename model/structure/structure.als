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
    or insertKey
    or keyOnPosition
    or lightRotaryToOff
    or lightRotaryToAuto
    or lightRotaryToOn
    or blinkCycle
    or activateBlinkingLeft
    or activateBlinkingRight
  )
}

pred nop {
  keyState' = keyState
  currentSpeed' = currentSpeed
  brakePedal' = brakePedal
  voltageBattery' = voltageBattery
  lightRotarySwitch' = lightRotarySwitch
  PitmanArmUpDown' = PitmanArmUpDown
  Actuator' = Actuator
  ActuatorWithLevel' = ActuatorWithLevel
  pitmanArmDegree'  = pitmanArmDegree 
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
}

pred insertKey {
  Vehicle . keyState = NoKeyInserted

  Vehicle . keyState' = KeyInserted

  currentSpeed'      = currentSpeed
  brakePedal'        = brakePedal
  voltageBattery'    = voltageBattery
  lightRotarySwitch' = lightRotarySwitch
  Actuator'          = Actuator
  ActuatorWithLevel' = ActuatorWithLevel
  pitmanArmDegree'  = pitmanArmDegree 
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
}

pred keyOnPosition {
  Vehicle . keyState = NoKeyInserted

  Vehicle . keyState' = KeyInIgnitionOnPosition
  // Activates Low Beam
  Vehicle . lightRotarySwitch = On
    => after (some LowBeamLeft and some LowBeamRight and mediumLowBeam)

  currentSpeed'      = currentSpeed
  brakePedal'        = brakePedal
  voltageBattery'    = voltageBattery
  lightRotarySwitch' = lightRotarySwitch
  Actuator'          = Actuator
  ActuatorWithLevel' = ActuatorWithLevel
  pitmanArmDegree'  = pitmanArmDegree 
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
}

pred lightRotaryToOff {
  Vehicle . lightRotarySwitch != Off

  Vehicle . lightRotarySwitch' = Off

  keyState'       = keyState
  currentSpeed'   = currentSpeed
  brakePedal'     = brakePedal
  voltageBattery' = voltageBattery
  PitmanArmUpDown'= PitmanArmUpDown
  Actuator'          = Actuator
  ActuatorWithLevel' = ActuatorWithLevel
  pitmanArmDegree'  = pitmanArmDegree 
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
}

pred lightRotaryToAuto {
  Vehicle . lightRotarySwitch != Auto

  Vehicle . lightRotarySwitch' = Auto

  keyState'       = keyState
  currentSpeed'   = currentSpeed
  brakePedal'     = brakePedal
  voltageBattery' = voltageBattery
  PitmanArmUpDown'= PitmanArmUpDown
  Actuator'          = Actuator
  ActuatorWithLevel' = ActuatorWithLevel
  pitmanArmDegree'  = pitmanArmDegree 
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
}

pred lightRotaryToOn {
  Vehicle . lightRotarySwitch != On

  Vehicle . lightRotarySwitch' = On
  // Activates Low Beam
  Vehicle . keyState = KeyInIgnitionOnPosition 
    => after (some LowBeamLeft and some LowBeamRight and mediumLowBeam)

  keyState'        = keyState
  currentSpeed'    = currentSpeed
  brakePedal'      = brakePedal
  voltageBattery'  = voltageBattery
  PitmanArmUpDown' = PitmanArmUpDown
  Actuator'          = Actuator
  ActuatorWithLevel' = ActuatorWithLevel
  pitmanArmDegree'  = pitmanArmDegree 
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
}

pred blinkCycle {
  some BlinkLeft + BlinkRight

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
  
  keyState'         = keyState
  currentSpeed'     = currentSpeed
  brakePedal'       = brakePedal
  voltageBattery'   = voltageBattery
  lightRotarySwitch'= lightRotarySwitch
  LowBeamLeft'      = LowBeamLeft
  LowBeamRight'     = LowBeamRight
  PitmanArmUpDown'  = PitmanArmUpDown
  pitmanArmDegree'  = pitmanArmDegree 
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
}

pred activateBlinkingLeft {
  no PitmanArmUpDown

  some PitmanArm . pitmanArmUpDown'
  after PitmanArmUpDown . pitmanArmUpDownPosition = Downward
  after PitmanArmUpDown . pitmanArmDegree = HighDegree
  after BlinkLeft . level = High

  keyState'          = keyState
  currentSpeed'      = currentSpeed
  brakePedal'        = brakePedal
  voltageBattery'    = voltageBattery
  lightRotarySwitch' = lightRotarySwitch
  LowBeamLeft'      = LowBeamLeft
  LowBeamRight'     = LowBeamRight
  BlinkRight'       = BlinkRight
}

pred activateBlinkingRight {
  no PitmanArmUpDown

  some PitmanArm . pitmanArmUpDown'
  after PitmanArmUpDown . pitmanArmUpDownPosition = Upward
  after PitmanArmUpDown . pitmanArmDegree = HighDegree
  after BlinkRight . level = High

  keyState'          = keyState
  currentSpeed'      = currentSpeed
  brakePedal'        = brakePedal
  voltageBattery'    = voltageBattery
  lightRotarySwitch' = lightRotarySwitch
  LowBeamLeft'       = LowBeamLeft
  LowBeamRight'      = LowBeamRight
  BlinkLeft'         = BlinkLeft
}
