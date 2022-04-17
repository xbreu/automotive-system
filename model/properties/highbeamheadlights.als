module properties/highbeamheadlights

open structure/structure

// ELS-30 | The headlamp flasher is activated by pulling the pitman arm, i.e.
// as long as the pitman arm is pulled 1©, the high beam headlight is
// activated.
check {
  //
}

// ELS-31 | If the light rotary switch is in position On, pushing the pitman
// arm to 4 causes the activation of the high beam headlight with a fixed
// illumination area of 220 m and 100 % luminous strength
// (i.e. highBeamMotor = 7 and highBeamRange = 100).
check {

}

// ELS-32 | If the light rotary switch is in position Auto, the adaptive high
// beam is activated by moving the pitman arm to the back 4.
check {

}

// ELS-33 | If adaptive high beam headlight is activated and the vehicle drives
// faster than 30 km/h and no light of an advancing vehicle is recognized by
// the camera, the street should be illuminated within 2 seconds according to
// the characteristic curve in Fig. 7 (for light illumination distance) and
// Fig. 8 (for luminous strength).
check {

}

// ELS-34 | If the camera recognizes the lights of an advancing vehicle, an
// activated high beam headlight is reduced to low beam headlight within 0.5
// seconds by reducing the area of illumination to 65 meters by an adjustment
// of the headlight position as well as by reduction of the luminous strength
// to 30%.
check {

}

// ELS-35 | If no advancing vehicle is recognized any more, the high beam
// illumination is restored after 2 seconds.
check {

}

// ELS-36 | The light illumination distance of the high beam headlight is
// within 100m and 300m, depending on the vehicle speed (see characteristic
// curve in Fig. 7).
check {

}

// ELS-37 | If an adaptive cruise control is part of the vehicle, the light
// illumination distance is not calculated upon the actual vehicle speed but
// the target speed provided by the advanced cruise control.
check {

}

// ELS-38 | If the pitman arm is moved again in the horizontal neutral
// position, the adaptive high beam headlight is deactivated. The illumination
// of the street is reduced immediately (i.e. without gentle fade-out) to low
// beam headlights.
check {

}
