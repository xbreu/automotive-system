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

pred parkingLights {
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

// ----------------------------------------------------------------------------
// Brake Light
// ----------------------------------------------------------------------------

pred activeBrakeLight {
  Vehicle . brakePedal = Medium
}

pred inactiveBrakeLight {
  Vehicle . brakePedal = Low
}

pred brakeLightCycle {
  eventually some BrakeLight
  eventually no BrakeLight
}

pred activateBrakeLightCycle {
  (
    always brakeLightCycle
  ) or (
    brakeLightCycle until Vehicle . brakePedal = Low
  )
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
  some PitmanArmBackward
  not subvoltage
  some CameraReadyVehicle
}

pred activeHighBeam {
  {
    some PitmanArmForward
  } or {
    Vehicle . lightRotarySwitch = On
    some PitmanArmBackward
  } or {
    activeAdaptiveHighBeam
    Vehicle . currentSpeed = High
  }

  no OncommingTrafficVehicle
}

pred inactiveHighBeam {
  not activeHighBeam
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
  // Deactivate normal blink
  not blinkingLeft
  // Deactivate tip blink (deactivates by itself after 3 cycles)

  // Also should deactivate when other blink action is performed
  blinkingRight or tipBlinkingRight
}

pred activeBlinkRight {
  blinkingRight or
  tipBlinkingRight
}

pred inactiveBlinkRight {
  // Deactivate normal blink
  not blinkingRight
  // Deactivate tip blink (deactivates by itself after 3 cycles)

  // Also should deactivate when other blink action is performed
  blinkingLeft or tipBlinkingLeft
}

// ----------------------------------------------------------------------------
// Low Beam
// ----------------------------------------------------------------------------

pred activeLowBeamLeft {
  Vehicle . keyState in KeyInserted + KeyInIgnitionOnPosition and
  (Vehicle . lightRotarySwitch = On or some DaytimeLights)
  or
  (Vehicle . lightRotarySwitch = Auto and 
    ignitionOnLock and
    Vehicle . brightnessSensor = Low)
  or
  (some AmbientLighting and 
    Vehicle . keyState in NoKeyInserted + KeyInserted and
    Vehicle . brightnessSensor = Low)
}

pred inactiveLowBeamLeft {
  (Vehicle . keyState != KeyInIgnitionOnPosition and
  Vehicle . lightRotarySwitch = Auto)
  or
  (Vehicle . lightRotarySwitch = Auto and 
  ignitionOnLock and
  Vehicle . brightnessSensor = High)
}

pred activeLowBeamRight {
  Vehicle . keyState in KeyInserted + KeyInIgnitionOnPosition and
  (Vehicle . lightRotarySwitch = On or some DaytimeLights)
  or
  (Vehicle . lightRotarySwitch = Auto and 
    ignitionOnLock and
    Vehicle . brightnessSensor = Low)
  or
  (some AmbientLighting and 
    Vehicle . keyState in NoKeyInserted + KeyInserted and
    Vehicle . brightnessSensor = Low)
}

pred inactiveLowBeamRight {
  (Vehicle . keyState != KeyInIgnitionOnPosition and
  Vehicle . lightRotarySwitch = Auto)
  or
  (Vehicle . lightRotarySwitch = Auto and 
  ignitionOnLock and
  Vehicle . brightnessSensor = High)
}

// ----------------------------------------------------------------------------
// Cornering Light
// ----------------------------------------------------------------------------

pred activeCorneringLightLeft {
  (
    (some LowBeam
      and (blinkingLeft or tipBlinkingLeft or some SteeringLeft)
      and Vehicle . currentSpeed = Low)
    or
    (
      some ReverseGearVehicle
    )
  )
  and not subvoltage
}

pred inactiveCorneringLightLeft {
  not activeCorneringLightLeft
}

pred activeCorneringLightRight {
  (
    (some LowBeam
      and (blinkingRight or tipBlinkingRight or some SteeringRight)
      and Vehicle . currentSpeed = Low)
    or
    (
      some ReverseGearVehicle
    )
  ) and not subvoltage
}

pred inactiveCorneringLightRight {
  not activeCorneringLightRight
}

// ----------------------------------------------------------------------------
// Tail Lamp
// ----------------------------------------------------------------------------

pred activeTailLampLeft {
  parkingLightCondition or
  Vehicle . brakePedal != Low or
  some LowBeam or
  some HighBeam
}

pred inactiveTailLampLeft {
  not parkingLightCondition and
  Vehicle . brakePedal = Low and
  no LowBeam and
  no HighBeam
}

pred activeTailLampRight {
  parkingLightCondition or
  Vehicle . brakePedal != Low or
  some LowBeam or
  some HighBeam
}

pred inactiveTailLampRight {
  not parkingLightCondition and
  Vehicle . brakePedal = Low and
  no LowBeam and
  no HighBeam
}

// ----------------------------------------------------------------------------
// Fault Handling
// ----------------------------------------------------------------------------

pred subvoltage {
  Vehicle . voltageBattery in Low
}

pred overvoltage {
  Vehicle . voltageBattery in High
}
