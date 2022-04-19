module properties/lowheadlightscorneringlight

open structure/structure

// ELS-14 | If the ignition is On and the light rotary switch is in the
// position On, then low beam headlights are activated.
check ELS14 {
  always (
    (Vehicle . keyState = KeyInIgnitionOnPosition and
    Vehicle . lightRotarySwitch = On) =>
    (some LowBeamLeft and some LowBeamRight)
  )
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
  always (
    Vehicle . keyState != KeyInIgnitionOnPosition and
    Vehicle . lightRotarySwitch = Auto =>
      after no LowBeamLeft + LowBeamRight 
  )
}

// ELS-17 | With activated daytime running light, the low beam headlights are
// activated after starting the engine. The daytime running light remains
// active as long as the ignition key is in the ignition lock (i.e. KeyInserted
// or KeyInIgnitionOnPosition). With additionally activated ambient light,
// ambient light control (Req. ELS-19) has priority over daytime running light.
check ELS17 {

}

// ELS-18 | If the light rotary switch is in position Auto and the ignition is
// On, the low beam headlights are activated as soon as the exterior brightness
// is lower than a threshold of 200 lx. If the exterior brightness exceeds a
// threshold of 250 lx, the low beam headlights are deactivated. In any case,
// the low beam headlights remain active at least for 3 seconds.
check ELS18 {

}

// ELS-19 | Ambient light prolongs (keeps low beam headlamps at 100% if they
// have been active before) the activation of low beam headlamps (as ambient
// light) if ambient light has been activated, engine has been stopped (i.e.
// keyState changes from KeyInIgnitionOnPosition to NoKeyInserted or
// KeyInserted) and the exterior brightness outside the vehicle is lower than
// the threshold 200 lx. In this case, the low beam headlamps remain active or
// are activated. The low beam headlights are deactivated or parking light is
// activated (see Req. ELS-28) after 30 seconds. This time interval is reset by
// - Opening or closing a door
// - Insertion or removal of the ignition key
check ELS19 {

}

// ELS-21 | With activated darkness switch (only armored vehicles) the ambient
// lighting is not activated. As long as the darkness switch is activated, it
// supresses low beam headlights due to ambient light.
check ELS21 {
  always (
    some Vehicle . darknessMode => no Vehicle . ambientLighting
  )
}

// ELS-22 | Whenever the low or high beam headlights are activated, the tail
// lights are activated, too.
check ELS22 {
  always (
    some LowBeamLeft + LowBeamRight + HighBeam
    => some TailLampLeft and some TailLampRight
  )
}

// ELS-23 | In USA or Canada, tail lights realize the direction indicator
// lamps. In case of direction blinking or hazard blinking, blinking has
// preference against normal tail lights.
check ELS23 {

}

// ELS-24 | Cornering light: If the low beam headlights are activated and
// direction blinking is requested, the cornering light is activated, when the
// vehicle drives slower than 10 km/h. 5 seconds after passing the corner (i.e.
// the direction blinking is not active any more for 5 seconds), the cornering
// light is switched off in a duration of 1 second (gentle fade-out).
// Activating cornering light means that if driving to the left is indicated,
// the left cornering light is activated. If driving to the right is indicated,
// the right cornering light shall be activated.
check ELS24 {

}

// ELS-25 | With activated darkness switch (only armored vehicles) the
// cornering light is not activated.
check ELS25 {

}

// ELS-26 | The cornering light is also activated, if the direction blinking is
// not activated, but all other constraints (see Req. ELS-24) are fulfilled and
// the steering wheel deflection is more than ±10◦.
check ELS26 {

}
