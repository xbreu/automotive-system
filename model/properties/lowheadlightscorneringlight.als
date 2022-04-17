module properties/lowheadlightscorneringlight

open structure/structure

// ELS-14 | If the ignition is On and the light rotary switch is in the
// position On, then low beam headlights are activated.
check ELS14 {
  (Vehicle . keyState = KeyInIgnitionOnPosition and
  Vehicle . lightRotarySwitch = On) =>
  (some LowBeamLeft and some LowBeamRight and
  some LowBeamLeft . level & LowBeamRight . level)
}

// ELS-15 | While the ignition is in position KeyInserted: if the light rotary
// switch is turned to the position On, the low beam headlights are activated
// with 50% (to save power). With additionally activated ambient light, ambient
// light control (Req. ELS-19) has priority over Req. ELS-15. With additionally
// activated daytime running light, Req. ELS-15 has priority over Req. ELS-17.
check ELS15 {
  always (
    Vehicle . keyState = KeyInserted => (
      Vehicle . lightRotarySwitch = On and
      (some daytimeLights or no ambientLighting)
      => mediumLowBeam
    )
  )
}

// ELS-16 | If the ignition is already off and the driver turns the light
// rotary switch to position Auto, the low beam headlights remain off or are
// deactivated (depending on the previous state). In case of conflict,
// Req. ELS-16 has priority over Req. ELS-17 (i.e. the later manual activitiy
// overrules running daytime light if ignition is KeyInserted). If ambient
// light is active (see Req. ELS-19), ambient light delays the deactivation of
// the low beam headlamps.
check ELS16 {

}

// ELS-17 | With activated daytime running light, the low beam headlights are
// activated after starting the engine. The daytime running light remains
// active as long as the ignition key is in the ignition lock (i.e. KeyInserted
// or KeyInIgnitionOnPosition). With additionally activated ambient light,
// ambient light control (Req. ELS-19) has priority over daytime running light.
check ELS17 {

}
