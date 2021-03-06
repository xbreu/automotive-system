module structure/signatures

// ----------------------------------------------------------------------------
// Auxiliary
// ----------------------------------------------------------------------------

abstract sig SwitchState {}
one sig Off, Auto, On
extends SwitchState {}

abstract sig Level {}
one sig Low, Medium, High
extends Level {}

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
  , var keyState: one KeyStatusAndPosition
  , var brightnessSensor: one Level // 200lx, 250lx
  , var brakePedal: one Level
  , var voltageBattery: one Level // 8.5V, 14.5V
  , var currentSpeed: one Level // 10 km/h, 30 km/h
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

abstract sig KeyStatusAndPosition {}
one sig NoKeyInserted, KeyInserted, KeyInIgnitionOnPosition
extends KeyStatusAndPosition {}

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

abstract sig PitmanArmDegree {}
one sig LowDegree, HighDegree
extends PitmanArmDegree {}

abstract sig PitmanArmUpDownPosition {}
one sig Downward, Upward
extends PitmanArmUpDownPosition {}

// ----------------------------------------------------------------------------
// Steering Wheel
// ----------------------------------------------------------------------------

lone var abstract sig SteeringWheel {}

lone var sig SteeringLeft
          ,  SteeringRight
    extends  SteeringWheel {}

// ----------------------------------------------------------------------------
// Aggregations of Signatures
// ----------------------------------------------------------------------------

fun Blink : (BlinkLeft + BlinkRight) {
  BlinkLeft + BlinkRight
}

fun LowBeam : (LowBeamLeft + LowBeamRight) {
  LowBeamLeft + LowBeamRight
}

fun CorneringLight : (CorneringLightLeft + CorneringLightRight) {
  CorneringLightLeft + CorneringLightRight
}
