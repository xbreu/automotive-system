module properties/faulthandlight

open structure/structure
open visualization

// ELS-42 | A subvoltage is present if the voltage in the vehicle electrical
// system is less than 8.5V. With subvoltage, the adaptive high beam headlight
// is not available.
check ELS42 {
  always (
    subvoltage => not activeAdaptiveHighBeam
  )
}

// ELS-43 | If the light rotary switch is in position Auto and the pitman arm
// is pulled, the high beam headlight is activated (see Req. ELS-31) even in
// case of subvoltage.
check ELS43 {
  always (
    (Vehicle . lightRotarySwitch in Auto and
    no OncommingTrafficVehicle and
    some PitmanArmForward)
    => some HighBeam
  )
}

// ELS-44 | With subvoltage the ambient light is not available.
check ELS44 {
  always (
    subvoltage => no AmbientLighting
  )
}

// ELS-45 | With subvoltage the cornering light is not available.
check ELS45 {
  always (
    subvoltage => no (CorneringLight)
  )
}

// ELS-46 | With subvoltage an activated parking light is switched off.
check ELS46 {
  always (
    not subvoltage
    and parkingLightCondition
    and (after subvoltage)
    => (after not parkingLights)
  )
}

// ELS-47 | An overvoltage is present if the voltage in the vehicle electrical
// system is more than 14.5V. With overvoltage, activated lights must not
// exceen the maximum light intensity of (100 - (voltage - 14.5) · 20)%. This
// reduction serves the protection of the illuminant (protection from "burning
// out").
check ELS47 {

}

// ELS-48 | With overvoltage, the illumination area requirements do not need to
// be respected (see Req. ELS-33 and Req. ELS-36). Instead, illumination area
// is fixed to 220m.
check ELS48 {

}

// ELS-49 | If the camera is not Ready, adaptive high beam headlights is not
// available. This means, if cameraState is unequal Ready, light rotary switch
// is in position Auto and the pitman arm is in position 4, manual high beam
// headlights are activated (see Req. ELS-31), which means that high beam
// headlights are activated with a fixed illumination area of 220m and 100%
// luminous strength (i.e. highBeamMotor = 7 and highBeamRange = 100).
check ELS49 {
  always (
    no CameraReadyVehicle => not activeAdaptiveHighBeam
  )
}
