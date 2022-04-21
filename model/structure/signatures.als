module structure/signatures

// ----------------------------------------------------------------------------
// Auxiliary
// ----------------------------------------------------------------------------

enum SwitchState {
  Off, Auto, On
}

enum Level {
  Low, Medium, High
}

// ----------------------------------------------------------------------------
// Actuators
// ----------------------------------------------------------------------------

abstract var sig Actuator {}

lone var sig BrakeLight
           , ReverseLight
     extends Actuator {}

lone var sig HighBeam
     extends Actuator {}

var sig HighRangeHighBeam
      , HighMotorHighBeam
     in HighBeam {}

abstract var sig ActuatorWithLevel {
  , var level: lone Level
}

lone var sig BlinkLeft
           , BlinkRight
           , LowBeamLeft
           , LowBeamRight
           , CorneringLightLeft
           , CorneringLightRight
           , TailLampLeft
           , TailLampRight
     extends ActuatorWithLevel {}

// ----------------------------------------------------------------------------
// Vehicle
// ----------------------------------------------------------------------------

one sig Vehicle {
  , var lightRotarySwitch: one SwitchState
  , var keyState: one KeyState
  , var brightnessSensor: one Level
  , var brakePedal: one Level
  , var voltageBattery: one Level
  , var currentSpeed: one Level
}

lone sig DaytimeLights
       , AmbientLighting
       , RightHandVehicle
       , NorthAmericanVehicle
      in Vehicle {}

var sig HazardWarningVehicle
      , ClosedDoorsVehicle
      , OncommingTrafficVehicle
      , CameraReadyVehicle
      , ReverseGearVehicle
     in Vehicle {}

sig ArmoredVehicle extends Vehicle {}

// User interface only available at armored vehicles
var sig DarknessModeVehicle
     in ArmoredVehicle {}

enum KeyState {
  NoKeyInserted, KeyInserted, KeyInIgnitionOnPosition
}

// ----------------------------------------------------------------------------
// Pitman Arm
// ----------------------------------------------------------------------------

lone var abstract sig PitmanArm {}

lone var sig PitmanArmUpDown extends PitmanArm {
  , var pitmanArmUpDownPosition: one PitmanArmUpDownPosition
  , var pitmanArmDegree: one PitmanArmDegree
}

lone var sig PitmanArmForward
           , PitmanArmBackward
     extends PitmanArm {}

enum PitmanArmDegree {
  LowDegree, HighDegree
}

enum PitmanArmUpDownPosition {
  Downward, Upward
}

// ----------------------------------------------------------------------------
// Aggregations of Signatures
// ----------------------------------------------------------------------------

fun Blink : (BlinkLeft + BlinkRight) {
  BlinkLeft + BlinkRight
}
