module properties/structural

open structure/structure

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
