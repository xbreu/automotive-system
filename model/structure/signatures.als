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

abstract var sig Actuator {}
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

lone var sig BrakeLight
       , ReverseLight
 extends Actuator {}

lone var sig HighBeam extends Actuator {
  , var highBeamHighRange: lone Yes
  , var highBeamHighMotor: lone Yes
}

// ----------------------------------------------------------------------------
// Vehicle
// ----------------------------------------------------------------------------

one sig Vehicle {
  // Car attributes
  , driverHand: one HorizontalDirection
  , marketCode: one MarketCode

  // User interface
  , var lightRotarySwitch: one SwitchState
  , var hazardWarning: lone Yes
  , daytimeLights: lone Yes
  , ambientLighting: lone Yes

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

lone var sig PitmanArmUpDown {
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
