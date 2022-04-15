module properties/structural

open structure as s

// Control of the low beam headlights. If daytime running light is activated,
// low beam headlights are active all the time and ambient light illuminates
// the vehicle surrounding while leaving the car during darkness. The function
// low beam headlight also includes parking light.
check daytimeLightsBeams {
  some daytimeLights => some LowBeamLeft and some LowBeamRight
}

// Direction blinking is only available when the ignition is on.
check directionDependsOnIgnition {
  (highBlinkLeft or highBlinkRight)
  => Vehicle . keyState = KeyInIgnitionOnPosition
}

// ELS-6 For cars sold in USA and Canada, the daytime running light must be
// dimmed by 50% during direction blinking on the blinking side.
check els6 {
  (Vehicle . marketCode = NorthAmerica and some daytimeLights)
  =>  (some BlinkLeft => LowBeamLeft . level = Medium)
  and (some BlinkRight => LowBeamRight . level = Medium)
}

// ELS-14 If the ignition is On and the light rotary switch is in the position
// On, then low beam headlights are activated.
check els14 {
  (Vehicle . keyState = KeyInIgnitionOnPosition and
   Vehicle . lightRotarySwitch = On) => some LowBeamLeft and some LowBeamRight
}

// ELS-21 With activated darkness switch (only armored vehicles) the ambient
// lighting is not activated.
check els21 {
  some Vehicle . darknessMode => no Vehicle . ambientLighting
}

// ELS-22 Whenever the low or high beam headlights are activated, the tail
// lights are activated, too.
check els22 {
  some LowBeamLeft + LowBeamRight + HighBeam
  => some TailLampLeft and some TailLampRight
}

// ELS-41 The reverse light is activated whenever the reverse gear is engaged.
check els41 {
  some Vehicle . reverseGear => some ReverseLight
}
