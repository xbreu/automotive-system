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

  no SteeringWheel
  no HazardWarningVehicle
  no PitmanArm
  no ReverseGearVehicle
  no OncommingTrafficVehicle
  some ClosedDoorsVehicle
  some CameraReadyVehicle
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

// ----------------------------------------------------------------------------
// Operations
// ----------------------------------------------------------------------------

fact traces {
  always {
    updateActuators

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

    mantainSteeringWheel
    or steeringWheelToNeutral
    or steeringWheelToLeft
    or steeringWheelToRight
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
  => {
    Vehicle . brakePedal' = High
    activateBrakeLightCycle
  }
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

pred mantainSteeringWheel {
  SteeringWheel' = SteeringWheel
  SteeringLeft' = SteeringLeft
  SteeringRight' = SteeringRight
}

pred steeringWheelToNeutral {
  // Guards
  some SteeringLeft + SteeringRight

  // Effects
  no (SteeringLeft + SteeringRight)'
}

pred steeringWheelToLeft {
  // Guards
  no SteeringLeft

  // Effects
  some SteeringLeft'
}

pred steeringWheelToRight {
  // Guards
  no SteeringRight

  // Effects
  some SteeringRight'
}

// ----------------------------------------------------------------------------
// Auxiliary Predicates
// ----------------------------------------------------------------------------

pred updateActuators {
  // Frame Conditions
  activeBrakeLight
  => some BrakeLight
  inactiveBrakeLight
  => no BrakeLight

  activeReverseLight
  => some ReverseLight
  inactiveReverseLight
  => no ReverseLight

  activeHighBeam
  => some HighBeam
  inactiveHighBeam
  => no HighBeam

  activeHighRangeHighBeam
  => some HighRangeHighBeam
  inactiveHighRangeHighBeam
  => no HighRangeHighBeam

  activeHighMotorHighBeam
  => some HighMotorHighBeam
  inactiveHighMotorHighBeam
  => no HighMotorHighBeam

  activeBlinkLeft
  => some BlinkLeft
  inactiveBlinkLeft
  => no BlinkLeft

  activeBlinkRight
  => some BlinkRight
  inactiveBlinkRight
  => no BlinkRight

  activeLowBeamLeft
  => some LowBeamLeft
  inactiveLowBeamLeft
  => no LowBeamLeft

  activeLowBeamRight
  => some LowBeamRight
  inactiveLowBeamRight
  => no LowBeamRight

  activeCorneringLightLeft
  => some CorneringLightLeft
  inactiveCorneringLightLeft
  => no CorneringLightLeft

  activeCorneringLightRight
  => some CorneringLightRight
  inactiveCorneringLightRight
  => no CorneringLightRight

  activeTailLampLeft
  => some TailLampLeft
  inactiveTailLampLeft
  => no TailLampLeft

  activeTailLampRight
  => some TailLampRight
  inactiveTailLampRight
  => no TailLampRight
}

// High beam is activated when adaptive high beam is active and the vehicle is
// driving fast in a road without oncoming traffic.
fact {
  {
    activeAdaptiveHighBeam
    Vehicle . currentSpeed = Medium
    no OncommingTrafficVehicle
  } => after some HighBeam
}

// While the ignition is in position KeyInserted: if the light rotary switch
// is turned to the position On, the low beam headlights are activated
// with 50% (to save power). With additionally activated ambient light,
// ambient light control (Req. ELS-19) has priority over Req. ELS-15.
// With additionally activated daytime running light, Req. ELS-15 has
// priority over Req. ELS-17.
fact {
  always {
    some LowBeam and
    Vehicle . keyState = KeyInserted and
    no AmbientLighting
    => LowBeam . level = Medium
  }
}

fact {
  always {
    Vehicle . keyState in NoKeyInserted and
    Vehicle . lightRotarySwitch in On and
    some PitmanArmUpDown
    =>
    parkingLights
  }
}

fact {
  always (
    {
      some OncommingTrafficVehicle
      before some HighBeam
    } => {
      no HighBeam
      some LowBeamLeft
      some LowBeamRight
    }
  )
}

fact {
  always (
    some HazardWarningVehicle => activateHazardWarning
  )
}

fact {
  always (
    subvoltage => no AmbientLighting
  )
}

fact {
  always {
    blinkingLeft => activateBlinkingLeft
    blinkingRight => activateBlinkingRight
    tipBlinkingLeft => blinkLeftThreeTimes
    tipBlinkingRight => blinkRightThreeTimes
  }
}

fact {
  always (
    some NorthAmericanVehicle and some DaytimeLights and ignitionOnLock
    => {
      blinkingLeft => LowBeamLeft . level = Medium
      blinkingRight => LowBeamRight . level = Medium
    }
  )
}

fact {
  always (
    some DarknessModeVehicle => no AmbientLighting
  )
}
