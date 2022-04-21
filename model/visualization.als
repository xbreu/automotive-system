module visualization

open structure/structure

// ----------------------------------------------------------------------------
// Actuators
// ----------------------------------------------------------------------------

one sig Actuators {}

abstract sig DummyActuator {}
abstract sig DummyActuatorWithLevel {}

lone sig DummyBlinkLeft
       , DummyBlinkRight
       , DummyLowBeamLeft
       , DummyLowBeamRight
       , DummyCorneringLightLeft
       , DummyCorneringLightRight
       , DummyTailLampLeft
       , DummyTailLampRight
extends DummyActuatorWithLevel {}

lone sig DummyBrakeLight
       , DummyReverseLight
       , DummyHighBeam
 extends DummyActuator {}

fun AllDummyActuators : set DummyActuator + DummyActuatorWithLevel {
  DummyActuator + DummyActuatorWithLevel
}

fact {
  one (BlinkLeft + DummyBlinkLeft)
  one (BlinkRight + DummyBlinkRight)
  one (LowBeamLeft + DummyLowBeamLeft)
  one (LowBeamRight + DummyLowBeamRight)
  one (CorneringLightLeft + DummyCorneringLightLeft)
  one (CorneringLightRight + DummyCorneringLightRight)
  one (TailLampLeft + DummyTailLampLeft)
  one (TailLampRight + DummyTailLampRight)
  one (BrakeLight + DummyBrakeLight)
  one (ReverseLight + DummyReverseLight)
  one (HighBeam + DummyHighBeam)
}

// ----------------------------------------------------------------------------
// Pitman Arm
// ----------------------------------------------------------------------------

lone sig PitmanArmUp
       , PitmanArmDown
       , PitmanArmLowDegree
       , PitmanArmHighDegree
       , DisabledPitmanArm
      in PitmanArm {}

fact {
  PitmanArmUpDown . pitmanArmUpDownPosition = Upward => one PitmanArmUp
  PitmanArmUpDown . pitmanArmUpDownPosition = Downward => one PitmanArmDown
  lone (PitmanArmUp + PitmanArmDown)

  PitmanArmUpDown . pitmanArmDegree = LowDegree => one PitmanArmLowDegree
  PitmanArmUpDown . pitmanArmDegree = HighDegree => one PitmanArmHighDegree
  lone (PitmanArmLowDegree + PitmanArmHighDegree)

  no PitmanArm => one DisabledPitmanArm
  no DisabledPitmanArm & (PitmanArmUp + PitmanArmDown + PitmanArmLowDegree
  + PitmanArmHighDegree)
}

// ----------------------------------------------------------------------------
// Hazard and Darkness Switches
// ----------------------------------------------------------------------------

abstract sig DummySwitch {}
lone sig HazardWarningOn
       , HazardWarningOff
       , DarknessModeOn
       , DarknessModeOff
       , AmbientLightingOn
       , AmbientLightingOff
       , DaytimeLightsOn
       , DaytimeLightsOff
 extends DummySwitch {}

fact {
  some HazardWarningVehicle => one HazardWarningOn
  one (HazardWarningOn + HazardWarningOff)

  some AmbientLighting => one AmbientLightingOn
  one (AmbientLightingOn + AmbientLightingOff)

  some DaytimeLights => one DaytimeLightsOn
  one (DaytimeLightsOn + DaytimeLightsOff)

  some DarknessModeVehicle => one DarknessModeOn
  lone (DarknessModeOn + DarknessModeOff)
  no ArmoredVehicle => no (DarknessModeOn + DarknessModeOff)
}

// ----------------------------------------------------------------------------
// Light Rotary Switch
// ----------------------------------------------------------------------------

one abstract sig LightRotary extends DummySwitch {}
lone sig LightRotaryOff
       , LightRotaryAuto
       , LightRotaryOn
 extends LightRotary {}

fact {
  Vehicle.lightRotarySwitch = Off  => one LightRotaryOff
  Vehicle.lightRotarySwitch = Auto => one LightRotaryAuto
  Vehicle.lightRotarySwitch = On   => one LightRotaryOn
}

// ----------------------------------------------------------------------------
// User Interface
// ----------------------------------------------------------------------------

one sig UserInterface {}
