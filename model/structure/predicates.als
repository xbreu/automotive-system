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

pred tipBlinkingLeft {
  PitmanArm . pitmanArmUpDown . pitmanArmUpDownPosition = Downward and
  PitmanArm . pitmanArmUpDown . pitmanArmDegree = LowDegree
}

pred tipBlinkingRight {
  PitmanArm . pitmanArmUpDown . pitmanArmUpDownPosition = Upward and
  PitmanArm . pitmanArmUpDown . pitmanArmDegree = LowDegree
}

pred parkingLight {
  some LowBeamLeft and some LowBeamRight
  some TailLampLeft and some TailLampRight
  LowBeamLeft . level & LowBeamRight . level = Low
  TailLampLeft . level & TailLampRight . level = Low
}
