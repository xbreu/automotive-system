module structure/predicates

open structure/signatures

pred ignitionOnLock {
  Vehicle . keyState in  KeyInserted + KeyInIgnitionOnPosition
}

pred directionBlinking {
  PitmanArm . pitmanArmUpDown . pitmanArmDegree = HighDegree
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
  PitmanArm . pitmanArmUpDown . pitmanArmUpDownPosition = Downward and
  PitmanArm . pitmanArmUpDown . pitmanArmDegree = HighDegree
}

pred blinkingRight {
  PitmanArm . pitmanArmUpDown . pitmanArmUpDownPosition = Upward and
  PitmanArm . pitmanArmUpDown . pitmanArmDegree = HighDegree
}

pred tipBlinkingLeft {
  PitmanArm . pitmanArmUpDown . pitmanArmUpDownPosition = Downward and
  PitmanArm . pitmanArmUpDown . pitmanArmDegree = LowDegree
}

pred tipBlinkingRight {
  PitmanArm . pitmanArmUpDown . pitmanArmUpDownPosition = Upward and
  PitmanArm . pitmanArmUpDown . pitmanArmDegree = LowDegree
}

pred parkingLight {
  Vehicle . keyState in NoKeyInserted
  Vehicle . lightRotarySwitch in On
  some pitmanArmUpDown

  ( LowBeamLeft   . level
  & LowBeamRight  . level
  & TailLampLeft  . level
  & TailLampRight . level) = Low
}

pred subvoltage {
  Vehicle . voltageBattery in Low
}

pred overvoltage {
  Vehicle . voltageBattery in High
}

pred pushingPitmanArm {
  PitmanArm . pitmanArmForthBack in Backward
}

pred pullingPitmanArm {
  PitmanArm . pitmanArmForthBack in Forward
}

pred adaptiveHighBeam {
  pushingPitmanArm and some HighBeam
}
