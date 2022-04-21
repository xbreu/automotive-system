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

fact fairness {
  //always eventually activateBlinkingLeft // Change this
}

// ----------------------------------------------------------------------------
// Operations
// ----------------------------------------------------------------------------

fact traces {
  always (
    nop
    or lightRotaryToOff
    or lightRotaryToAuto
    or lightRotaryToOn
    or enableHazardWarning
    or disableHazardWarning
    or removeKey
    or insertKey
    or putKeyOnPosition
    or removeKeyFromPosition
    or brightnessSensorToLow
    or brightnessSensorToMedium
    or brightnessSensorToHigh
    or brakePedalUp
    or brakePedalDown
    or voltageBatteryToLow
    or voltageBatteryToMedium
    or voltageBatteryToHigh
    or closeDoors
    or openDoors
    or enableOncommingTraffic
    or disableOncommingTraffic
    or enableCameraReady
    or disableCameraReady
    or currentSpeedUp
    or currentSpeedDown
    or enableReverseGear
    or disableReverseGear
    or enableDarknessMode
    or disableDarknessMode
    or deactivatePitmanArm
    or some p: PitmanArmUpDownPosition, d: PitmanArmDegree | pitmanArmToUpDown[p, d]
    or pitmanArmToForward
    or pitmanArmToBackward
  )
}

pred nop {
  // Frame conditions
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
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred lightRotaryToOff {
  // Guards
  Vehicle . lightRotarySwitch != Off

  // Effects
  Vehicle . lightRotarySwitch' = Off
  updateActuators

  // Frame conditions
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
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred lightRotaryToAuto {
  // Guards
  Vehicle . lightRotarySwitch != Auto

  // Effects
  Vehicle . lightRotarySwitch' = Auto
  updateActuators

  // Frame conditions
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
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred lightRotaryToOn {
  // Guards
  Vehicle . lightRotarySwitch != On

  // Effects
  Vehicle . lightRotarySwitch' = On
  updateActuators

  // Frame conditions
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
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred enableHazardWarning {
  // Guards
  no hazardWarning

  // Effects
  some hazardWarning
  updateActuators

  // Frame conditions
  lightRotarySwitch'       = lightRotarySwitch
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
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred disableHazardWarning {
  // Guards
  some hazardWarning

  // Effects
  no hazardWarning
  updateActuators

  // Frame conditions
  lightRotarySwitch'       = lightRotarySwitch
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
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred removeKey {
  // Guards
  Vehicle . keyState = KeyInserted

  // Effects
  Vehicle . keyState' = NoKeyInserted
  updateActuators

  // Frame conditions
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
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred insertKey {
  // Guards
  Vehicle . keyState = NoKeyInserted

  // Effects
  Vehicle . keyState' = KeyInserted
  updateActuators

  // Frame conditions
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
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred removeKeyFromPosition {
  // Guards
  Vehicle . keyState = KeyInIgnitionOnPosition

  // Effects
  Vehicle . keyState' = KeyInserted
  updateActuators

  // Frame conditions
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
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred putKeyOnPosition {
  // Guards
  Vehicle . keyState = KeyInserted

  // Effects
  Vehicle . keyState' = KeyInIgnitionOnPosition
  updateActuators

  // Frame conditions
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
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred brightnessSensorToLow {
  // Guards
  Vehicle . brightnessSensor != Low

  // Effects
  Vehicle . brightnessSensor = Low
  updateActuators

  // Frame conditions
  lightRotarySwitch'       = lightRotarySwitch
  hazardWarning'           = hazardWarning
  keyState'                = keyState
  brakePedal'              = brakePedal
  voltageBattery'          = voltageBattery
  closedDoors'             = closedDoors
  oncommingTraffic'        = oncommingTraffic
  cameraReady'             = cameraReady
  currentSpeed'            = currentSpeed
  reverseGear'             = reverseGear
  darknessMode'            = darknessMode
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred brightnessSensorToMedium {
  // Guards
  Vehicle . brightnessSensor != Medium

  // Effects
  Vehicle . brightnessSensor = Medium
  updateActuators

  // Frame conditions
  lightRotarySwitch'       = lightRotarySwitch
  hazardWarning'           = hazardWarning
  keyState'                = keyState
  brakePedal'              = brakePedal
  voltageBattery'          = voltageBattery
  closedDoors'             = closedDoors
  oncommingTraffic'        = oncommingTraffic
  cameraReady'             = cameraReady
  currentSpeed'            = currentSpeed
  reverseGear'             = reverseGear
  darknessMode'            = darknessMode
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred brightnessSensorToHigh {
  // Guards
  Vehicle . brightnessSensor != High

  // Effects
  Vehicle . brightnessSensor = High
  updateActuators

  // Frame conditions
  lightRotarySwitch'       = lightRotarySwitch
  hazardWarning'           = hazardWarning
  keyState'                = keyState
  brakePedal'              = brakePedal
  voltageBattery'          = voltageBattery
  closedDoors'             = closedDoors
  oncommingTraffic'        = oncommingTraffic
  cameraReady'             = cameraReady
  currentSpeed'            = currentSpeed
  reverseGear'             = reverseGear
  darknessMode'            = darknessMode
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred brakePedalUp {
  // Guards
  Vehicle . brakePedal != High

  // Effects
  Vehicle . brakePedal = Low
  => Vehicle . brakePedal' = Medium
  Vehicle . brakePedal = Medium
  => Vehicle . brakePedal' = High
  updateActuators

  // Frame conditions
  lightRotarySwitch'       = lightRotarySwitch
  hazardWarning'           = hazardWarning
  keyState'                = keyState
  brightnessSensor'        = brightnessSensor
  voltageBattery'          = voltageBattery
  closedDoors'             = closedDoors
  oncommingTraffic'        = oncommingTraffic
  cameraReady'             = cameraReady
  currentSpeed'            = currentSpeed
  reverseGear'             = reverseGear
  darknessMode'            = darknessMode
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred brakePedalDown {
  // Guards
  Vehicle . brakePedal != Low

  // Effects
  Vehicle . brakePedal = Medium
  => Vehicle . brakePedal' = Low
  Vehicle . brakePedal = High
  => Vehicle . brakePedal' = Medium
  updateActuators

  // Frame conditions
  lightRotarySwitch'       = lightRotarySwitch
  hazardWarning'           = hazardWarning
  keyState'                = keyState
  brightnessSensor'        = brightnessSensor
  voltageBattery'          = voltageBattery
  closedDoors'             = closedDoors
  oncommingTraffic'        = oncommingTraffic
  cameraReady'             = cameraReady
  currentSpeed'            = currentSpeed
  reverseGear'             = reverseGear
  darknessMode'            = darknessMode
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred voltageBatteryToLow {
  // Guards

  // Effects

  updateActuators


}

pred voltageBatteryToLow {
  // Guards

  // Effects

  updateActuators


}

pred voltageBatteryToHigh {
  // Guards

  // Effects

  updateActuators


}

pred closeDoors {
  // Guards

  // Effects

  updateActuators


}

pred openDoors {
  // Guards

  // Effects

  updateActuators


}

pred enableOncommingTraffic {
  // Guards

  // Effects

  updateActuators


}

pred disableOncommingTraffic {
  // Guards

  // Effects

  updateActuators


}

pred enableCameraReady {
  // Guards

  // Effects

  updateActuators


}

pred disableCameraReady {
  // Guards

  // Effects

  updateActuators


}

pred currentSpeedUp {
  // Guards

  // Effects

  updateActuators


}

pred currentSpeedDown {
  // Guards

  // Effects

  updateActuators


}

pred enableReverseGear {
  // Guards

  // Effects

  updateActuators


}

pred disableReverseGear {
  // Guards

  // Effects

  updateActuators


}

pred enableDarknessMode {
  // Guards

  // Effects

  updateActuators


}

pred disableDarknessMode {
  // Guards

  // Effects

  updateActuators


}

pred deactivatePitmanArm {
  // Guards

  // Effects

  updateActuators


}

pred deactivatePitmanArm {
  // Guards

  // Effects

  updateActuators


}

pred pitmanArmToUpDown[p: PitmanArmUpDownPosition, d: PitmanArmDegree] {
  // Guards

  // Effects

  updateActuators


}

pred pitmanArmToForward {
  // Guards

  // Effects

  updateActuators


}

pred pitmanArmToBackward {
  // Guards

  // Effects

  updateActuators


}

// --------------------------------------------------------

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

pred voltageBatteryDown {
  // Guard
  Vehicle . voltageBattery != Low

  // Effects
  Vehicle . voltageBattery = Medium =>
    Vehicle . voltageBattery' = Low
  Vehicle . voltageBattery = High =>
    Vehicle . voltageBattery' = Medium


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

pred voltageBatteryUp {
  // Guard
  Vehicle . voltageBattery != High

  // Effects
  Vehicle . voltageBattery = Low =>
    Vehicle . voltageBattery' = Medium
  Vehicle . voltageBattery = Medium =>
    Vehicle . voltageBattery' = High


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

// ----------------------------------------------------------------------------
// Auxiliary Predicates
// ----------------------------------------------------------------------------

pred updateActuators {
  // Frame Conditions
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
