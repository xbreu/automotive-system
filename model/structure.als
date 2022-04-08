module structure

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
lone sig Blink, LowBeam, CorneringLight, TailLamp extends Actuator {
  , direction: one HorizontalDirection
}

lone sig BrakeLight, ReverseLight extends Actuator {}
lone sig HighBeam extends Actuator {
  , highBeamRange: Int
  , highBeamMotor: Int
}

// ----------------------------------------------------------------------------
// Vehicle
// ----------------------------------------------------------------------------

one sig Vehicle {
  // Enumeration attributes
  , driverHand: one HorizontalDirection
  , marketCode: one MarketCode
  , keyState: one KeyState
  , lightRotarySwitch: one SwitchState
  , brightnessSensor: one Level
  , brakePedal: one Level
  , currentSpeed: one Level

  // Boolean attributes
  , hazardWarning: lone Yes
  , closedDoors: lone Yes
  , oncommingTraffic: lone Yes
  , reverseGear: lone Yes
  , cameraReady: lone Yes
  , daytimeLights: lone Yes
  , ambientLighting: lone Yes
}

sig ArmoredVehicle extends Vehicle {
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
  , pitmanArmForthBack: lone PitmanArmForthBack
  , pitmanArmUpDown: lone PitmanArmUpDown
}

lone sig PitmanArmUpDown {
  , pitmanArmUpDownPosition: one PitmanArmUpDownPosition
  , pitmanArmDegree: one PitmanArmDegree
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
