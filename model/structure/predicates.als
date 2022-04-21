module structure/predicates

open structure/signatures

pred ignitionOnLock {
  Vehicle . keyState in  KeyInserted + KeyInIgnitionOnPosition
}

pred directionBlinking {
  some PitmanArmUpDown . pitmanArmUpDownPosition
  PitmanArmUpDown . pitmanArmDegree = HighDegree
}

pred engineOn {
  Vehicle . keyState = KeyInIgnitionOnPosition
}

pred mediumLowBeam {
  LowBeamLeft . level = Medium
  LowBeamRight . level = Medium
}

pred lowBlinkLeft {
  some BlinkLeft and BlinkLeft . level = Low
}

pred highBlinkLeft {
  some BlinkLeft and BlinkLeft . level = High
}

pred lowBlinkRight {
  some BlinkRight and BlinkRight . level = Low
}

pred highBlinkRight {
  some BlinkRight and BlinkRight . level = High
}

pred blinkingLeft {
  PitmanArmUpDown . pitmanArmUpDownPosition = Downward
  PitmanArmUpDown . pitmanArmDegree = HighDegree
}

pred blinkingRight {
  PitmanArmUpDown . pitmanArmUpDownPosition = Upward
  PitmanArmUpDown . pitmanArmDegree = HighDegree
}

pred tipBlinkingLeft {
  PitmanArmUpDown . pitmanArmUpDownPosition = Downward
  PitmanArmUpDown . pitmanArmDegree = LowDegree
}

pred tipBlinkingRight {
  PitmanArmUpDown . pitmanArmUpDownPosition = Upward
  PitmanArmUpDown . pitmanArmDegree = LowDegree
}

pred parkingLight {
  Vehicle . keyState in NoKeyInserted
  Vehicle . lightRotarySwitch in On
  some PitmanArmUpDown

  ( LowBeamLeft   . level
  & LowBeamRight  . level
  & TailLampLeft  . level
  & TailLampRight . level) = Low
}

pred parkingLightCondition {
  Vehicle . keyState in NoKeyInserted
  Vehicle . lightRotarySwitch in On
  some PitmanArmUpDown
}

pred subvoltage {
  Vehicle . voltageBattery in Low
}

pred overvoltage {
  Vehicle . voltageBattery in High
}

pred pushingPitmanArm {
  some PitmanArmBackward
}

pred pullingPitmanArm {
  some PitmanArmForward
}

pred adaptiveHighBeam {
  pushingPitmanArm and some HighBeam
}

// ----------------------------------------------------------------------------
// Brake Light
// ----------------------------------------------------------------------------

pred activeBrakeLight {
  Vehicle . brakePedal = Medium
}

pred inactiveBrakeLight {
  Vehicle . brakePedal = Low
}

// ----------------------------------------------------------------------------
// Reverse Light
// ----------------------------------------------------------------------------

pred activeReverseLight {
  some ReverseGearVehicle
}

pred inactiveReverseLight {
  no ReverseGearVehicle
}

// ----------------------------------------------------------------------------
// High Beam
// ----------------------------------------------------------------------------

pred activeAdaptiveHighBeam {
  Vehicle . lightRotarySwitch = Auto
  and some PitmanArmBackward
}

pred activeHighBeam {
  (some PitmanArmForward)
  or (some PitmanArmBackward)
}

pred inactiveHighBeam {

}

pred activeHighRangeHighBeam {
  activeHighBeam and {

  }
}

pred inactiveHighRangeHighBeam {
  inactiveHighBeam or {
    some PitmanArmBackward
  }
}

pred activeHighMotorHighBeam {
  activeHighBeam and {

  }
}

pred inactiveHighMotorHighBeam {
  inactiveHighBeam or {
    some PitmanArmBackward
  }
}

// ----------------------------------------------------------------------------
// Blinking Lights
// ----------------------------------------------------------------------------

pred activeBlinkLeft {
  blinkingLeft or
  tipBlinkingLeft
}

pred inactiveBlinkLeft {

}

pred activeBlinkRight {
  blinkingRight or
  tipBlinkingRight
}

pred inactiveBlinkRight {

}

// ----------------------------------------------------------------------------
// Low Beam
// ----------------------------------------------------------------------------

pred activeLowBeamLeft {
  Vehicle . keyState in KeyInserted + KeyInIgnitionOnPosition and
  (Vehicle . lightRotarySwitch = On or some DaytimeLights)
}

pred inactiveLowBeamLeft {
  Vehicle . keyState != KeyInIgnitionOnPosition and
  Vehicle . lightRotarySwitch = Auto
}

pred activeLowBeamRight {
  Vehicle . keyState in KeyInserted + KeyInIgnitionOnPosition and
  (Vehicle . lightRotarySwitch = On or some DaytimeLights)
}

pred inactiveLowBeamRight {
  Vehicle . keyState != KeyInIgnitionOnPosition and
  Vehicle . lightRotarySwitch = Auto
}

// ----------------------------------------------------------------------------
// Cornering Light
// ----------------------------------------------------------------------------

pred activeCorneringLightLeft {
  (some LowBeam 
    and (blinkingLeft or tipBlinkingLeft or some SteeringLeft) 
    and Vehicle . currentSpeed = Low)
  or
  (
    some ReverseGearVehicle
  )
}

pred inactiveCorneringLightLeft {
  not (some LowBeam 
    and (blinkingLeft or tipBlinkingLeft or some SteeringLeft) 
    and Vehicle . currentSpeed = Low) and
  no ReverseGearVehicle
}

pred activeCorneringLightRight {
  (some LowBeam 
    and (blinkingRight or tipBlinkingRight or some SteeringRight) 
    and Vehicle . currentSpeed = Low)
  or
  (
    some ReverseGearVehicle
  )
}

pred inactiveCorneringLightRight {
  not (some LowBeam 
    and (blinkingRight or tipBlinkingRight or some SteeringRight) 
    and Vehicle . currentSpeed = Low) and
  no ReverseGearVehicle
}

// ----------------------------------------------------------------------------
// Tail Lamp
// ----------------------------------------------------------------------------

pred activeTailLampLeft {
  parkingLightCondition or Vehicle . brakePedal != Low
}

pred inactiveTailLampLeft {
  not parkingLightCondition and Vehicle . brakePedal = Low
}

pred activeTailLampRight {
  parkingLightCondition or Vehicle . brakePedal != Low
}

pred inactiveTailLampRight {
  not parkingLightCondition and Vehicle . brakePedal = Low
}
