module properties/directionblinking

open structure/structure

// ELS-1 | Direction blinking left: When moving the pitman arm in position
// "turn left" 3 , the vehicle flashes all left direction indicators (front
// left, exterior mirror left, rear left) synchronously with pulse ratio bright
// to dark 1:1 and a frequency of 1.0 Hz ± 0.1 Hz (i.e. 60 flashes per minute
// ± 6 flashes).
check ELS1 {
  always (
    blinkingLeft => activateBlinkingLeft
  )
}

// ELS-2 | Tip-blinking left: If the driver moves the pitman arm for less than
// 0.5 seconds in position "Tip-blinking left", all left direction indicators
// (see Req. ELS-1) should flash for three flashing cycles.
check ELS2 {
  always (
    tipBlinkingLeft => (
      blinkLeftThreeTimes
    )
  )
}


// ELS-3 | If the driver activates the pitman arm in another direction or
// activates the hazard warning light switch during the three flashing cycles
// of the tip-blinking, the tip-blinking cycle must be stopped and the
// requested flashing cycle must be started (i.e. direction blinking,
// tip-blinking, or hazard warning light, depending on the interrupting
// request).
check ELS3 {
  always (
    tipBlinkingLeft => blinkLeftThreeTimes
    or eventually (
      some HazardWarningVehicle
      or blinkingRight
      or tipBlinkingRight
    )
  )
}


// ELS-4 | If the driver holds the pitman arm for more than 0.5 seconds in
// position "tip-blinking left", flashing cycles are initiated for all
// direction indicators on the left (see Req. ELS-1) until the pitman arm
// leaves the position "tip-blinking left".
check ELS4 {
  always (
    tipBlinkingLeft => (
      always
      activateBlinkingLeft
      and tipBlinkingLeft
    ) or (
      activateBlinkingLeft
      until not tipBlinkingLeft
    )
  )
}

// ELS-5 | Direction blinking right and tip-blinking right: Analogous to the
// left side (see Req. Req. ELS-1 to Req. ELS-4).
check ELS5 {
  always (
    blinkingRight => activateBlinkingRight
  )

  always (
    tipBlinkingRight => (
      blinkRightThreeTimes
    )
  )

  always (
    tipBlinkingRight => blinkRightThreeTimes
    or eventually (
      some HazardWarningVehicle
      or blinkingRight
      or tipBlinkingRight
    )
  )

  always (
    tipBlinkingRight => (
      always
      activateBlinkingRight
      and tipBlinkingRight
    ) or (
      activateBlinkingRight
      until not tipBlinkingRight
    )
  )
}

// ELS-6 | For cars sold in USA and Canada, the daytime running light must be
// dimmed by 50% during direction blinking on the blinking side.
check ELS6 {
  always (
    some NorthAmericanVehicle and some DaytimeLights and ignitionOnLock
    => {
      blinkingLeft => LowBeamLeft . level = Medium
      blinkingRight => LowBeamRight . level = Medium
    }
  )
}

// ELS-7 | If the driver activates the pitman arm during the three flashing
// cycles of tip-blinking for the same direction again, only the current
// flashing cycle is completed and then the new command is processed (either
// three flashing cycles due to tip-blinking or constant direction blinking).
check ELS7 {

}
