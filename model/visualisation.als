module visualisation

open structure as s

// ----------------------------------------------------------------------------
// Actuators
// ----------------------------------------------------------------------------

one sig Actuators {}

abstract sig DummyActuator {}
lone sig Blink
       , LowBeam
       , CorneringLight
       , TailLamp
       , BrakeLight
       , ReverseLight
       , HighBeam
 extends DummyActuator {}

fact {
  one (s/Blink + this/Blink)
  one (s/LowBeam + this/LowBeam)
  one (s/CorneringLight + this/CorneringLight)
  one (s/TailLamp + this/TailLamp)
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

  no (PitmanArm - (pitmanArmForthBack . PitmanArmForthBack)
  - (pitmanArmUpDown . PitmanArmUpDown)) => one DisabledPitmanArm
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