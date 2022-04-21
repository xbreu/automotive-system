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
// Actuator activation
// ----------------------------------------------------------------------------

pred activeBrakeLight {

}

pred inactiveBrakeLight {

}

pred activeReverseLight {

}

pred inactiveReverseLight {

}

pred activeHighBeam {

}

pred inactiveHighBeam {

}

pred activeHighRangeHighBeam {
  activeHighBeam and {

  }
}

pred inactiveHighRangeHighBeam {
  inactiveHighBeam or {

  }
}

pred activeHighMotorHighBeam {
  activeHighBeam and {

  }
}

pred inactiveHighMotorHighBeam {
  inactiveHighBeam or {

  }
}

pred activeBlinkLeft {

}

pred inactiveBlinkLeft {

}

pred activeBlinkRight {

}

pred inactiveBlinkRight {

}

pred activeLowBeamLeft {

}

pred inactiveLowBeamLeft {

}

pred activeLowBeamRight {

}

pred inactiveLowBeamRight {

}

pred activeCorneringLightLeft {

}

pred inactiveCorneringLightLeft {

}

pred activeCorneringLightRight {

}

pred inactiveCorneringLightRight {

}

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
