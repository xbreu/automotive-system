module structure/structure

open structure/predicates

// ----------------------------------------------------------------------------
// Initial Configuration
// ----------------------------------------------------------------------------

fact init {
  Vehicle . lightRotarySwitch = Off
  Vehicle . keyState          = NoKeyInserted
  Vehicle . brakePedal        = Low
  Vehicle . voltageBattery    = Medium

  no hazardWarning

  Vehicle . currentSpeed      = Low

  some closedDoors
  no PitmanArm
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
    or switchHazardWarning
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
    or switchClosedDoors
    or switchOncommingTraffic
    or switchCameraReady
    or currentSpeedUp
    or currentSpeedDown
    or switchReverseGear
    or switchDarknessMode
    or deactivatePitmanArm
    or some p: PitmanArmUpDownPosition, d: PitmanArmDegree | pitmanArmToUpDown[p, d]
    or pitmanArmToForward
    or pitmanArmToBackward
  ) and updateActuators
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

pred switchHazardWarning {
  // Effects
  some hazardWarning
  => no hazardWarning'
  no hazardWarning
  => some hazardWarning'
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
  Vehicle . brightnessSensor' = Low
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
  Vehicle . brightnessSensor' = Medium
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
  Vehicle . brightnessSensor' = High
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
  Vehicle . voltageBattery != Low

  // Effects
  Vehicle . voltageBattery' = Low
  updateActuators

  // Frame conditions
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
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred voltageBatteryToMedium {
  // Guards
  Vehicle . voltageBattery != Medium

  // Effects
  Vehicle . voltageBattery' = Medium
  updateActuators

  // Frame conditions
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
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred voltageBatteryToHigh {
  // Guards
  Vehicle . voltageBattery != High

  // Effects
  Vehicle . voltageBattery' = High
  updateActuators

  // Frame conditions
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
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred switchClosedDoors {
  // Effects
  no Vehicle . closedDoors
  => some Vehicle . closedDoors'
  some Vehicle . closedDoors
  => no Vehicle . closedDoors'
  updateActuators

  // Frame conditions
  lightRotarySwitch'       = lightRotarySwitch
  hazardWarning'           = hazardWarning
  keyState'                = keyState
  brightnessSensor'        = brightnessSensor
  brakePedal'              = brakePedal
  voltageBattery'          = voltageBattery
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

pred switchOncommingTraffic {
  // Effects
  no Vehicle . oncommingTraffic
  => some Vehicle . oncommingTraffic'
  some Vehicle . oncommingTraffic
  => no Vehicle . oncommingTraffic'
  updateActuators

  // Frame conditions
  lightRotarySwitch'       = lightRotarySwitch
  hazardWarning'           = hazardWarning
  keyState'                = keyState
  brightnessSensor'        = brightnessSensor
  brakePedal'              = brakePedal
  voltageBattery'          = voltageBattery
  closedDoors'             = closedDoors
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

pred switchCameraReady {
  // Effects
  no Vehicle . cameraReady
  => some Vehicle . cameraReady'
  some Vehicle . cameraReady
  => no Vehicle . cameraReady'
  updateActuators

  // Frame conditions
  lightRotarySwitch'       = lightRotarySwitch
  hazardWarning'           = hazardWarning
  keyState'                = keyState
  brightnessSensor'        = brightnessSensor
  brakePedal'              = brakePedal
  voltageBattery'          = voltageBattery
  closedDoors'             = closedDoors
  oncommingTraffic'        = oncommingTraffic
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

pred currentSpeedUp {
  // Guards
  Vehicle . currentSpeed != High

  // Effects
  Vehicle . currentSpeed = Low
  => Vehicle . currentSpeed' = Medium
  Vehicle . currentSpeed = Medium
  => Vehicle . currentSpeed' = High
  updateActuators

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
  reverseGear'             = reverseGear
  darknessMode'            = darknessMode
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred currentSpeedDown {
  // Guards
  Vehicle . currentSpeed != Low

  // Effects
  Vehicle . currentSpeed = Medium
  => Vehicle . currentSpeed' = Low
  Vehicle . currentSpeed = High
  => Vehicle . currentSpeed' = Medium
  updateActuators

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
  reverseGear'             = reverseGear
  darknessMode'            = darknessMode
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred switchReverseGear {
  // Effects
  no Vehicle . reverseGear
  => some Vehicle . reverseGear'
  some Vehicle . reverseGear
  => no Vehicle . reverseGear'
  updateActuators

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
  darknessMode'            = darknessMode
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred switchDarknessMode {
  // Effects
  some Vehicle . darknessMode
  => no Vehicle . darknessMode'
  no Vehicle . darknessMode
  => some Vehicle . darknessMode'
  updateActuators

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
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred deactivatePitmanArm {
  // Guards
  some PitmanArm

  // Effects
  no PitmanArm'
  updateActuators

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
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred pitmanArmToUpDown[p: PitmanArmUpDownPosition, d: PitmanArmDegree] {
  // Guards
  no PitmanArmUpDown
  or PitmanArmUpDown . pitmanArmUpDownPosition != p
  or PitmanArmUpDown . pitmanArmDegree != d

  // Effects
  some PitmanArmUpDown'
  PitmanArmUpDown . pitmanArmUpDownPosition' = p
  PitmanArmUpDown . pitmanArmDegree' = d
  updateActuators

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
}

pred pitmanArmToForward {
  // Guards
  no PitmanArmForward

  // Effects
  some PitmanArmForward'
  updateActuators

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
}

pred pitmanArmToBackward {
  // Guards
  no PitmanArmBackward

  // Effects
  some PitmanArmBackward'
  updateActuators

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
