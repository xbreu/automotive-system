module interface

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
// Ambient
// ----------------------------------------------------------------------------

one sig Ambient {
  , daytime: lone Yes
  , lighting: lone Yes
}

// ----------------------------------------------------------------------------
// Actuators
// ----------------------------------------------------------------------------

abstract sig Actuator {}
lone sig Blink, LowBeam, CorneringLight, TailLamp extends Actuator {
  , direction: one HorizontalDirection
}

lone sig BrakeLight, ReverseLight extends Actuator {}
lone sig HighBeam {
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
  , var keyState: one KeyState
  , var lightRotarySwitch: one SwitchState

  // Numerical attributes
  , var currentSpeed: one Int

  // Boolean attributes
  , var brightnessSensor: one Level
  , var brakePedal: one Level
  , var hazardWarning: lone Yes
  , var engineOn: lone Yes
  , var closedDoors: lone Yes
  , var oncommingTraffic: lone Yes
  , var reverseGear: lone Yes
  , var cameraReady: lone Yes
}

sig ArmoredVehicle extends Vehicle {
  , var darknessMode: lone Yes
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
  , var pitmanArmForthBack: one PitmanArmForthBack
  , pitmanArmUpDown: one PitmanArmUpDown
}

one sig PitmanArmUpDown {
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
