module structure/signatures

// ----------------------------------------------------------------------------
// Auxiliary
// ----------------------------------------------------------------------------

one sig Yes {}

enum HorizontalDirection {
  Right, Left
}

enum SwitchState {
  Off, Auto, On
}

enum Level {
  Low, Medium, High
}

// ----------------------------------------------------------------------------
// Actuators
// ----------------------------------------------------------------------------

abstract sig Actuator {}
abstract sig ActuatorWithLevel {
  , level: lone Level
}

lone sig BlinkLeft
       , BlinkRight
       , LowBeamLeft
       , LowBeamRight
       , CorneringLightLeft
       , CorneringLightRight
       , TailLampLeft
       , TailLampRight
 extends ActuatorWithLevel {}

lone sig BrakeLight
       , ReverseLight
 extends Actuator {}

lone sig HighBeam extends Actuator {
  , highBeamHighRange: lone Yes
  , highBeamHighMotor: lone Yes
}

// ----------------------------------------------------------------------------
// Vehicle
// ----------------------------------------------------------------------------

one sig Vehicle {
  // Car attributes
  , var driverHand: one HorizontalDirection
  , var marketCode: one MarketCode

  // User interface
  , var lightRotarySwitch: one SwitchState
  , var hazardWarning: lone Yes
  , var daytimeLights: lone Yes
  , var ambientLighting: lone Yes

  // Sensors
  , var keyState: one KeyState
  , var brightnessSensor: one Level
  , var brakePedal: one Level
  , var voltageBattery: one Level
  , var closedDoors: lone Yes
  , var oncommingTraffic: lone Yes
  , var cameraReady: lone Yes
  , var currentSpeed: one Level
  , var reverseGear: lone Yes
}

sig ArmoredVehicle extends Vehicle {
  // User interface only available at armored vehicles
  , darknessMode: lone Yes
}

enum KeyState {
  NoKeyInserted, KeyInserted, KeyInIgnitionOnPosition
}

enum MarketCode {
  NorthAmerica, Other
}

// ----------------------------------------------------------------------------
// Pitman Arm
// ----------------------------------------------------------------------------

one sig PitmanArm {
  , var pitmanArmForthBack: lone PitmanArmForthBack
  , var pitmanArmUpDown: lone PitmanArmUpDown
}

lone sig PitmanArmUpDown {
  , var pitmanArmUpDownPosition: one PitmanArmUpDownPosition
  , var pitmanArmDegree: one PitmanArmDegree
}

enum PitmanArmDegree {
  LowDegree, HighDegree
}

enum PitmanArmUpDownPosition {
  Downward, Upward
}

enum PitmanArmForthBack {
  Backward, Forward
}

// ----------------------------------------------------------------------------
// Aggregations of Signatures
// ----------------------------------------------------------------------------

fun Blink : (BlinkLeft + BlinkRight) {
  BlinkLeft + BlinkRight
}
