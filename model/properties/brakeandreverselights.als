module properties/brakeandreverselights

open structure/structure
open visualization

// ELS-39 | If the brake pedal is deflected more than 3, all brake lamps have
// to be activated until the deflection is lower than 1 again.
check ELS39 {
  always (
    Vehicle . brakePedal = Medium =>
    ((some BrakeLight) until (Vehicle . brakePedal != Medium))
    or (always some BrakeLight)
  )
}

// ELS-40 | If the brake pedal is deflected more than 40.0◦ (i.e. full-brake
// application), all brake lamps flash with pulse ratio bright to dark 1:1 and
// a frequency of 6±1 Hz (i.e. 360±60 flashes per minute). The flashing stops
// only when the brake pedal is in its neutral position again
// (i.e. brakePedal = 0).
check ELS40 {

}

// ELS-41 | The reverse light is activated whenever the reverse gear is
// engaged.
check ELS41 {
  always (
    some ReverseGearVehicle => some ReverseLight
  )
}
