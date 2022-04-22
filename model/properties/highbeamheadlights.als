module properties/highbeamheadlights

open structure/structure
open visualization

// ELS-30 | The headlamp flasher is activated by pulling the pitman arm, i.e.
// as long as the pitman arm is pulled 1©, the high beam headlight is
// activated.
check ELS30 {
  always (
    some PitmanArmForward and not {
      // ELS34
      some OncommingTrafficVehicle
    } => some HighBeam
  )
}

// ELS-31 | If the light rotary switch is in position On, pushing the pitman
// arm to 4 causes the activation of the high beam headlight with a fixed
// illumination area of 220 m and 100 % luminous strength
// (i.e. highBeamMotor = 7 and highBeamRange = 100).
check ELS31 {
  always (
    Vehicle . lightRotarySwitch = On and some PitmanArmForward and not {
      // ELS34
      some OncommingTrafficVehicle
    } => some HighBeam
  )
}

// ELS-32 | If the light rotary switch is in position Auto, the adaptive high
// beam is activated by moving the pitman arm to the back 4.
check ELS32 {
  always (
    Vehicle . lightRotarySwitch = Auto and some PitmanArmBackward =>
    activeAdaptiveHighBeam
  )
}

// ELS-33 | If adaptive high beam headlight is activated and the vehicle drives
// faster than 30 km/h and no light of an advancing vehicle is recognized by
// the camera, the street should be illuminated within 2 seconds according to
// the characteristic curve in Fig. 7 (for light illumination distance) and
// Fig. 8 (for luminous strength).
check ELS33 {
  always (
    {
      activeAdaptiveHighBeam
      Vehicle . currentSpeed = High
      no OncommingTrafficVehicle
    } and not {
      // ELS34
      some OncommingTrafficVehicle
    } => some HighBeam
  )
}

// ELS-34 | If the camera recognizes the lights of an advancing vehicle, an
// activated high beam headlight is reduced to low beam headlight within 0.5
// seconds by reducing the area of illumination to 65 meters by an adjustment
// of the headlight position as well as by reduction of the luminous strength
// to 30%.
check ELS34 {
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

// ELS-35 | If no advancing vehicle is recognized any more, the high beam
// illumination is restored after 2 seconds.
check ELS35 {

}

// ELS-36 | The light illumination distance of the high beam headlight is
// within 100m and 300m, depending on the vehicle speed (see characteristic
// curve in Fig. 7).
check ELS36 {

}

// ELS-37 | If an adaptive cruise control is part of the vehicle, the light
// illumination distance is not calculated upon the actual vehicle speed but
// the target speed provided by the advanced cruise control.
check ELS37 {
  // This is not useful for our problem because we did not model the cruise
  // control, as it is only needed for the speed control system. So, the
  // abstraction was that the current speed is already the right one, that
  // is maybe calculated by the advanced cruise control.
}

// ELS-38 | If the pitman arm is moved again in the horizontal neutral
// position, the adaptive high beam headlight is deactivated. The illumination
// of the street is reduced immediately (i.e. without gentle fade-out) to low
// beam headlights.
check ELS38 {
  always (
    {
      no PitmanArm
      before activeAdaptiveHighBeam
    } => {
      not activeAdaptiveHighBeam
      no HighBeam
    }
  )
}
