module visualisation

open structure as s

// ----------------------------------------------------------------------------
// Actuators
// ----------------------------------------------------------------------------

one sig Actuators {}

abstract sig DummyActuator {}
abstract sig DummyActuatorWithLevel {}

lone sig BlinkLeft
       , BlinkRight
       , LowBeamLeft
       , LowBeamRight
       , CorneringLightLeft
       , CorneringLightRight
       , TailLampLeft
       , TailLampRight
extends DummyActuatorWithLevel {}

lone sig BrakeLight
       , ReverseLight
       , HighBeam
 extends DummyActuator {}

fact {
  one (s/BlinkLeft + this/BlinkLeft)
  one (s/BlinkRight + this/BlinkRight)
  one (s/LowBeamLeft + this/LowBeamLeft)
  one (s/LowBeamRight + this/LowBeamRight)
  one (s/CorneringLightLeft + this/CorneringLightLeft)
  one (s/CorneringLightRight + this/CorneringLightRight)
  one (s/TailLampLeft + this/TailLampLeft)
  one (s/TailLampRight + this/TailLampRight)
  one (s/BrakeLight + this/BrakeLight)
  one (s/ReverseLight + this/ReverseLight)
  one (s/HighBeam + this/HighBeam)
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
  one pitmanArmUpDown . pitmanArmUpDownPosition . Upward => one PitmanArmUp
  one pitmanArmUpDown . pitmanArmUpDownPosition . Downward => one PitmanArmDown
  lone (PitmanArmUp + PitmanArmDown)

  one pitmanArmUpDown . pitmanArmDegree . LowDegree => one PitmanArmLowDegree
  one pitmanArmUpDown . pitmanArmDegree . HighDegree => one PitmanArmHighDegree
  lone (PitmanArmLowDegree + PitmanArmHighDegree)

  no PitmanArmForthBack and no PitmanArmUpDown => one DisabledPitmanArm
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
  some Vehicle . hazardWarning => one HazardWarningOn
  one (HazardWarningOn + HazardWarningOff)
  
  some Vehicle . ambientLighting => one AmbientLightingOn
  one (AmbientLightingOn + AmbientLightingOff)

  some Vehicle . daytimeLights => one DaytimeLightsOn
  one (DaytimeLightsOn + DaytimeLightsOff)

  some ArmoredVehicle . darknessMode => one DarknessModeOn
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