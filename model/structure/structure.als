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
  //always eventually activateBlinkingLeft // Change this
}

fact traces {
  always (
    nop
    or insertKey
    or putKeyOnPosition
    or lightRotaryToOff
    or lightRotaryToAuto
    or lightRotaryToOn
    or blinkCycle
    or activateBlinkingLeft
    or deactivateBlinkingLeft
    or activateBlinkingRight
    or deactivateBlinkingRight
    or pullPitmanArm
    or pushPitmanArm
  )
}

pred nop {
  // Frame conditions
  Actuator'                = Actuator
  ActuatorWithLevel'       = ActuatorWithLevel
  level'                   = level
  BlinkLeft'               = BlinkLeft
  BlinkRight'              = BlinkRight
  LowBeamLeft'             = LowBeamLeft
  LowBeamRight'            = LowBeamRight
  CorneringLightLeft'      = CorneringLightLeft
  CorneringLightRight'     = CorneringLightRight
  TailLampLeft'            = TailLampLeft
  TailLampRight'           = TailLampRight
  BrakeLight'              = BrakeLight
  ReverseLight'            = ReverseLight
  HighBeam'                = HighBeam
  highBeamHighRange'       = highBeamHighRange
  highBeamHighMotor'       = highBeamHighMotor
  lightRotarySwitch'       = lightRotarySwitch
  hazardWarning'           = hazardWarning
  keyState'                = keyState
  brightnessSensor'        = brightnessSensor
  brakePedal'              = brakePedal
  voltageBattery'          = voltageBattery
  closedDoors'             = closedDoors
  oncommingTraffic'        = oncommingTraffic
  cameraReady'             = cameraReady
  currentSpeed'            = currentSpeed
  reverseGear'             = reverseGear
  darknessMode'            = darknessMode
  pitmanArmForthBack'      = pitmanArmForthBack
  pitmanArmUpDown'         = pitmanArmUpDown
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
}

pred insertKey {
  // Guards
  Vehicle . keyState = NoKeyInserted

  // Effects
  Vehicle . keyState' = KeyInserted

  // Frame conditions
  Actuator'                = Actuator
  ActuatorWithLevel'       = ActuatorWithLevel
  level'                   = level
  BlinkLeft'               = BlinkLeft
  BlinkRight'              = BlinkRight
  LowBeamLeft'             = LowBeamLeft
  LowBeamRight'            = LowBeamRight
  CorneringLightLeft'      = CorneringLightLeft
  CorneringLightRight'     = CorneringLightRight
  TailLampLeft'            = TailLampLeft
  TailLampRight'           = TailLampRight
  BrakeLight'              = BrakeLight
  ReverseLight'            = ReverseLight
  HighBeam'                = HighBeam
  highBeamHighRange'       = highBeamHighRange
  highBeamHighMotor'       = highBeamHighMotor
  lightRotarySwitch'       = lightRotarySwitch
  hazardWarning'           = hazardWarning
  brightnessSensor'        = brightnessSensor
  brakePedal'              = brakePedal
  voltageBattery'          = voltageBattery
  closedDoors'             = closedDoors
  oncommingTraffic'        = oncommingTraffic
  cameraReady'             = cameraReady
  currentSpeed'            = currentSpeed
  reverseGear'             = reverseGear
  darknessMode'            = darknessMode
  pitmanArmForthBack'      = pitmanArmForthBack
  pitmanArmUpDown'         = pitmanArmUpDown
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
}

pred putKeyOnPosition {
  // Guards
  Vehicle . keyState = NoKeyInserted

  // Effects
  Vehicle . keyState' = KeyInIgnitionOnPosition
  activateLowBeam

  // Frame conditions
  Actuator'                = Actuator
  ActuatorWithLevel'       = ActuatorWithLevel
  BlinkLeft'               = BlinkLeft
  BlinkRight'              = BlinkRight
  CorneringLightLeft'      = CorneringLightLeft
  CorneringLightRight'     = CorneringLightRight
  TailLampLeft'            = TailLampLeft
  TailLampRight'           = TailLampRight
  BrakeLight'              = BrakeLight
  ReverseLight'            = ReverseLight
  HighBeam'                = HighBeam
  highBeamHighRange'       = highBeamHighRange
  highBeamHighMotor'       = highBeamHighMotor
  lightRotarySwitch'       = lightRotarySwitch
  hazardWarning'           = hazardWarning
  brightnessSensor'        = brightnessSensor
  brakePedal'              = brakePedal
  voltageBattery'          = voltageBattery
  closedDoors'             = closedDoors
  oncommingTraffic'        = oncommingTraffic
  cameraReady'             = cameraReady
  currentSpeed'            = currentSpeed
  reverseGear'             = reverseGear
  darknessMode'            = darknessMode
  pitmanArmForthBack'      = pitmanArmForthBack
  pitmanArmUpDown'         = pitmanArmUpDown
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
}

pred lightRotaryToOff {
  // Guards
  Vehicle . lightRotarySwitch != Off

  // Effects
  Vehicle . lightRotarySwitch' = Off

  // Frame conditions
  Actuator'                = Actuator
  ActuatorWithLevel'       = ActuatorWithLevel
  level'                   = level
  BlinkLeft'               = BlinkLeft
  BlinkRight'              = BlinkRight
  LowBeamLeft'             = LowBeamLeft
  LowBeamRight'            = LowBeamRight
  CorneringLightLeft'      = CorneringLightLeft
  CorneringLightRight'     = CorneringLightRight
  TailLampLeft'            = TailLampLeft
  TailLampRight'           = TailLampRight
  BrakeLight'              = BrakeLight
  ReverseLight'            = ReverseLight
  HighBeam'                = HighBeam
  highBeamHighRange'       = highBeamHighRange
  highBeamHighMotor'       = highBeamHighMotor
  hazardWarning'           = hazardWarning
  keyState'                = keyState
  brightnessSensor'        = brightnessSensor
  brakePedal'              = brakePedal
  voltageBattery'          = voltageBattery
  closedDoors'             = closedDoors
  oncommingTraffic'        = oncommingTraffic
  cameraReady'             = cameraReady
  currentSpeed'            = currentSpeed
  reverseGear'             = reverseGear
  darknessMode'            = darknessMode
  pitmanArmForthBack'      = pitmanArmForthBack
  pitmanArmUpDown'         = pitmanArmUpDown
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
}

pred lightRotaryToAuto {
  Vehicle . lightRotarySwitch != Auto

  Vehicle . lightRotarySwitch' = Auto

  // Frame conditions
  Actuator'                = Actuator
  ActuatorWithLevel'       = ActuatorWithLevel
  level'                   = level
  BlinkLeft'               = BlinkLeft
  BlinkRight'              = BlinkRight
  LowBeamLeft'             = LowBeamLeft
  LowBeamRight'            = LowBeamRight
  CorneringLightLeft'      = CorneringLightLeft
  CorneringLightRight'     = CorneringLightRight
  TailLampLeft'            = TailLampLeft
  TailLampRight'           = TailLampRight
  BrakeLight'              = BrakeLight
  ReverseLight'            = ReverseLight
  HighBeam'                = HighBeam
  highBeamHighRange'       = highBeamHighRange
  highBeamHighMotor'       = highBeamHighMotor
  hazardWarning'           = hazardWarning
  keyState'                = keyState
  brightnessSensor'        = brightnessSensor
  brakePedal'              = brakePedal
  voltageBattery'          = voltageBattery
  closedDoors'             = closedDoors
  oncommingTraffic'        = oncommingTraffic
  cameraReady'             = cameraReady
  currentSpeed'            = currentSpeed
  reverseGear'             = reverseGear
  darknessMode'            = darknessMode
  pitmanArmForthBack'      = pitmanArmForthBack
  pitmanArmUpDown'         = pitmanArmUpDown
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
}

pred lightRotaryToOn {
  // Guards
  Vehicle . lightRotarySwitch != On

  // Effects
  Vehicle . lightRotarySwitch' = On
  activateLowBeam

  // Frame conditions
  Actuator'                = Actuator
  ActuatorWithLevel'       = ActuatorWithLevel
  level'                   = level
  BlinkLeft'               = BlinkLeft
  BlinkRight'              = BlinkRight
  LowBeamLeft'             = LowBeamLeft
  LowBeamRight'            = LowBeamRight
  CorneringLightLeft'      = CorneringLightLeft
  CorneringLightRight'     = CorneringLightRight
  TailLampLeft'            = TailLampLeft
  TailLampRight'           = TailLampRight
  BrakeLight'              = BrakeLight
  ReverseLight'            = ReverseLight
  HighBeam'                = HighBeam
  highBeamHighRange'       = highBeamHighRange
  highBeamHighMotor'       = highBeamHighMotor
  lightRotarySwitch'       = lightRotarySwitch
  hazardWarning'           = hazardWarning
  keyState'                = keyState
  brightnessSensor'        = brightnessSensor
  brakePedal'              = brakePedal
  voltageBattery'          = voltageBattery
  closedDoors'             = closedDoors
  oncommingTraffic'        = oncommingTraffic
  cameraReady'             = cameraReady
  currentSpeed'            = currentSpeed
  reverseGear'             = reverseGear
  darknessMode'            = darknessMode
  pitmanArmForthBack'      = pitmanArmForthBack
  pitmanArmUpDown'         = pitmanArmUpDown
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
}

pred blinkCycle {
  // Guards
  some BlinkLeft + BlinkRight

  // Effects
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

  // Frame conditions
  Actuator'                = Actuator
  ActuatorWithLevel'       = ActuatorWithLevel
  level'                   = level
  LowBeamLeft'             = LowBeamLeft
  LowBeamRight'            = LowBeamRight
  CorneringLightLeft'      = CorneringLightLeft
  CorneringLightRight'     = CorneringLightRight
  TailLampLeft'            = TailLampLeft
  TailLampRight'           = TailLampRight
  BrakeLight'              = BrakeLight
  ReverseLight'            = ReverseLight
  HighBeam'                = HighBeam
  highBeamHighRange'       = highBeamHighRange
  highBeamHighMotor'       = highBeamHighMotor
  lightRotarySwitch'       = lightRotarySwitch
  hazardWarning'           = hazardWarning
  keyState'                = keyState
  brightnessSensor'        = brightnessSensor
  brakePedal'              = brakePedal
  voltageBattery'          = voltageBattery
  closedDoors'             = closedDoors
  oncommingTraffic'        = oncommingTraffic
  cameraReady'             = cameraReady
  currentSpeed'            = currentSpeed
  reverseGear'             = reverseGear
  darknessMode'            = darknessMode
  pitmanArmForthBack'      = pitmanArmForthBack
  pitmanArmUpDown'         = pitmanArmUpDown
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
}

pred activateBlinkingLeft {
  // Guards
  no PitmanArmUpDown

  // Effects
  some PitmanArm . pitmanArmUpDown'
  after PitmanArmUpDown . pitmanArmUpDownPosition = Downward
  after PitmanArmUpDown . pitmanArmDegree = HighDegree
  after BlinkLeft . level = High

  // Frame conditions
  keyState'          = keyState
  currentSpeed'      = currentSpeed
  brakePedal'        = brakePedal
  voltageBattery'    = voltageBattery
  hazardWarning'     = hazardWarning
  lightRotarySwitch' = lightRotarySwitch
  LowBeamLeft'       = LowBeamLeft
  LowBeamRight'      = LowBeamRight
  BlinkRight'        = BlinkRight
}

pred deactivateBlinkingLeft {
  // Guards
  blinkingLeft

  // Effects
  no PitmanArm . pitmanArmUpDown'
  no pitmanArmUpDownPosition'
  no pitmanArmDegree'
  no BlinkLeft'

  // Frame conditions
  keyState'          = keyState
  currentSpeed'      = currentSpeed
  brakePedal'        = brakePedal
  voltageBattery'    = voltageBattery
  hazardWarning'     = hazardWarning
  lightRotarySwitch' = lightRotarySwitch
  LowBeamLeft'       = LowBeamLeft
  LowBeamRight'      = LowBeamRight
  BlinkRight'        = BlinkRight
}

pred activateBlinkingRight {
  // Guards
  no PitmanArmUpDown

  // Effects
  some PitmanArm . pitmanArmUpDown'
  after PitmanArmUpDown . pitmanArmUpDownPosition = Upward
  after PitmanArmUpDown . pitmanArmDegree = HighDegree
  after BlinkRight . level = High

  // Frame conditions
  keyState'          = keyState
  currentSpeed'      = currentSpeed
  brakePedal'        = brakePedal
  voltageBattery'    = voltageBattery
  hazardWarning'     = hazardWarning
  lightRotarySwitch' = lightRotarySwitch
  LowBeamLeft'       = LowBeamLeft
  LowBeamRight'      = LowBeamRight
  BlinkLeft'         = BlinkLeft
}

pred deactivateBlinkingRight {
  // Guards
  blinkingRight

  // Effects
  no PitmanArm . pitmanArmUpDown'
  no pitmanArmUpDownPosition'
  no pitmanArmDegree'
  no BlinkRight'

  // Frame conditions
  keyState'          = keyState
  currentSpeed'      = currentSpeed
  brakePedal'        = brakePedal
  voltageBattery'    = voltageBattery
  hazardWarning'     = hazardWarning
  lightRotarySwitch' = lightRotarySwitch
  LowBeamLeft'       = LowBeamLeft
  LowBeamRight'      = LowBeamRight
  BlinkLeft'         = BlinkLeft
}

pred activateLowBeam {
  Vehicle . lightRotarySwitch = On
    => after {
      some LowBeamLeft
      some LowBeamRight
      level' = level
         - ((LowBeamLeft + LowBeamRight) <: level)
         + ((LowBeamLeft + LowBeamRight) -> Medium)
    } else {
      LowBeamLeft'  = LowBeamLeft
      LowBeamRight' = LowBeamRight
      level'        = level
    }
}

pred pullPitmanArm {
  // Guards
  no PitmanArm . pitmanArmForthBack

  // Effects
  PitmanArm . pitmanArmForthBack' = Forward

  // Frame conditions
  Actuator'                = Actuator
  ActuatorWithLevel'       = ActuatorWithLevel
  level'                   = level
  LowBeamLeft'             = LowBeamLeft
  LowBeamRight'            = LowBeamRight
  CorneringLightLeft'      = CorneringLightLeft
  CorneringLightRight'     = CorneringLightRight
  TailLampLeft'            = TailLampLeft
  TailLampRight'           = TailLampRight
  BrakeLight'              = BrakeLight
  ReverseLight'            = ReverseLight
  HighBeam'                = HighBeam
  highBeamHighRange'       = highBeamHighRange
  highBeamHighMotor'       = highBeamHighMotor
  lightRotarySwitch'       = lightRotarySwitch
  hazardWarning'           = hazardWarning
  keyState'                = keyState
  brightnessSensor'        = brightnessSensor
  brakePedal'              = brakePedal
  voltageBattery'          = voltageBattery
  closedDoors'             = closedDoors
  oncommingTraffic'        = oncommingTraffic
  cameraReady'             = cameraReady
  currentSpeed'            = currentSpeed
  reverseGear'             = reverseGear
  darknessMode'            = darknessMode
  pitmanArmUpDown'         = pitmanArmUpDown
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
}

pred pushPitmanArm {
  // Guards
  no PitmanArm . pitmanArmForthBack

  // Effects
  PitmanArm . pitmanArmForthBack' = Backward

  // Frame conditions
  Actuator'                = Actuator
  ActuatorWithLevel'       = ActuatorWithLevel
  level'                   = level
  LowBeamLeft'             = LowBeamLeft
  LowBeamRight'            = LowBeamRight
  CorneringLightLeft'      = CorneringLightLeft
  CorneringLightRight'     = CorneringLightRight
  TailLampLeft'            = TailLampLeft
  TailLampRight'           = TailLampRight
  BrakeLight'              = BrakeLight
  ReverseLight'            = ReverseLight
  HighBeam'                = HighBeam
  highBeamHighRange'       = highBeamHighRange
  highBeamHighMotor'       = highBeamHighMotor
  lightRotarySwitch'       = lightRotarySwitch
  hazardWarning'           = hazardWarning
  keyState'                = keyState
  brightnessSensor'        = brightnessSensor
  brakePedal'              = brakePedal
  voltageBattery'          = voltageBattery
  closedDoors'             = closedDoors
  oncommingTraffic'        = oncommingTraffic
  cameraReady'             = cameraReady
  currentSpeed'            = currentSpeed
  reverseGear'             = reverseGear
  darknessMode'            = darknessMode
  pitmanArmUpDown'         = pitmanArmUpDown
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
}
