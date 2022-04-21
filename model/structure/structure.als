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
  Vehicle . currentSpeed      = Low

  no HazardWarningVehicle
  no PitmanArm
  no ReverseGearVehicle
  no OncommingTrafficVehicle
  some ClosedDoorsVehicle
  some CameraReadyVehicle

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
    some DaytimeLights => some LowBeamLeft and some LowBeamRight
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
  always {
    mantainKey
    or removeKey
    or insertKey
    or putKeyOnPosition
    or removeKeyFromPosition

    mantainBrakePedal
    or increaseBrakePedal
    or decreaseBrakePedal

    mantainCurrentSpeed
    or increaseCurrentSpeed
    or decreaseCurrentSpeed

    mantainPitmanArm
    or deactivatePitmanArm
    or pitmanArmToForward
    or pitmanArmToBackward
    or (some p: PitmanArmUpDownPosition, d: PitmanArmDegree | pitmanArmToUpDown[p, d])

    updateActuators
  }
}

pred nop {
  // Frame conditions
  lightRotarySwitch'       = lightRotarySwitch
  keyState'                = keyState
  brightnessSensor'        = brightnessSensor
  brakePedal'              = brakePedal
  voltageBattery'          = voltageBattery
  currentSpeed'            = currentSpeed
  HazardWarningVehicle'    = HazardWarningVehicle
  ClosedDoorsVehicle'      = ClosedDoorsVehicle
  OncommingTrafficVehicle' = OncommingTrafficVehicle
  CameraReadyVehicle'      = CameraReadyVehicle
  ReverseGearVehicle'      = ReverseGearVehicle
  DarknessModeVehicle'     = DarknessModeVehicle
  PitmanArm'               = PitmanArm
  PitmanArmUpDown'         = PitmanArmUpDown
  pitmanArmUpDownPosition' = pitmanArmUpDownPosition
  pitmanArmDegree'         = pitmanArmDegree
  PitmanArmForward'        = PitmanArmForward
  PitmanArmBackward'       = PitmanArmBackward
}

pred mantainKey {
  // Frame Conditions
  keyState' = keyState
}

pred removeKey {
  // Guards
  Vehicle . keyState = KeyInserted

  // Effects
  Vehicle . keyState' = NoKeyInserted
}

pred insertKey {
  // Guards
  Vehicle . keyState = NoKeyInserted

  // Effects
  Vehicle . keyState' = KeyInserted
}

pred removeKeyFromPosition {
  // Guards
  Vehicle . keyState = KeyInIgnitionOnPosition

  // Effects
  Vehicle . keyState' = KeyInserted
}

pred putKeyOnPosition {
  // Guards
  Vehicle . keyState = KeyInserted

  // Effects
  Vehicle . keyState' = KeyInIgnitionOnPosition
}

pred mantainBrakePedal {
  // Frame Conditions
  brakePedal' = brakePedal
}

pred increaseBrakePedal {
  // Guards
  Vehicle . brakePedal != High

  // Effects
  Vehicle . brakePedal = Low
  => Vehicle . brakePedal' = Medium
  Vehicle . brakePedal = Medium
  => Vehicle . brakePedal' = High
}

pred decreaseBrakePedal {
  // Guards
  Vehicle . brakePedal != Low

  // Effects
  Vehicle . brakePedal = Medium
  => Vehicle . brakePedal' = Low
  Vehicle . brakePedal = High
  => Vehicle . brakePedal' = Medium
}

pred mantainCurrentSpeed {
  // Frame Conditions
  currentSpeed' = currentSpeed
}

pred increaseCurrentSpeed {
  // Guards
  Vehicle . currentSpeed != High

  // Effects
  Vehicle . currentSpeed = Low
  => Vehicle . currentSpeed' = Medium
  Vehicle . currentSpeed = Medium
  => Vehicle . currentSpeed' = High
}

pred decreaseCurrentSpeed {
  // Guards
  Vehicle . currentSpeed != Low

  // Effects
  Vehicle . currentSpeed = Medium
  => Vehicle . currentSpeed' = Low
  Vehicle . currentSpeed = High
  => Vehicle . currentSpeed' = Medium
}

pred mantainPitmanArm {
  // Frame Conditions
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
}

pred pitmanArmToUpDown[p: PitmanArmUpDownPosition, d: PitmanArmDegree] {
  // Guards
  no PitmanArmUpDown
  or PitmanArmUpDown . pitmanArmUpDownPosition != p
  or PitmanArmUpDown . pitmanArmDegree != d

  // Effects
  some PitmanArmUpDown'
  (PitmanArmUpDown . pitmanArmUpDownPosition)' = p
  (PitmanArmUpDown . pitmanArmDegree)' = d
}

pred pitmanArmToForward {
  // Guards
  no PitmanArmForward

  // Effects
  some PitmanArmForward'
}

pred pitmanArmToBackward {
  // Guards
  no PitmanArmBackward

  // Effects
  some PitmanArmBackward'
}

// ----------------------------------------------------------------------------
// Auxiliary Predicates
// ----------------------------------------------------------------------------

pred updateActuators {
  // Frame Conditions
  Actuator'                = Actuator
  BrakeLight'              = BrakeLight
  ReverseLight'            = ReverseLight
  HighBeam'                = HighBeam
  HighRangeHighBeam'       = HighRangeHighBeam
  HighMotorHighBeam'       = HighMotorHighBeam
  ActuatorWithLevel'       = ActuatorWithLevel
  BlinkLeft'               = BlinkLeft
  BlinkRight'              = BlinkRight
  LowBeamLeft'             = LowBeamLeft
  LowBeamRight'            = LowBeamRight
  CorneringLightLeft'      = CorneringLightLeft
  CorneringLightRight'     = CorneringLightRight
  TailLampLeft'            = TailLampLeft
  TailLampRight'           = TailLampRight
}
