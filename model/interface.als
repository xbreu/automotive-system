module interface

one sig Yes {}

one sig Ambient {
  , daytime: one Yes
  , lighting: one Yes
}

abstract sig Actuator {}
lone sig Blink, LowBeam, CorneringLight, TailLamp extends Actuator {
  , direction: one Direction
}

lone sig BrakeLight, ReverseLight extends Actuator {}
lone sig HighBeam {
  , highBeamRange: Int
  , highBeamMotor: Int
}

one sig Vehicle {
  // Enumeration attributes
  , driverPosition: one DriverPosition
  , marketCode: one MarketCode
  , var keyState: one KeyState
  , var lightRotarySwitch: one LightRotarySwitch

  // Numerical attributes
  , var currentSpeed: one Int

  // Boolean attributes
  , var brightnessSensor: one BrightnessState
  , var brakePedal: one BreakState
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

one sig PitmanArm {
  , var pitmanArmForthBack: one PitmanArmForthBack
  , pitmanArmUpDown: one PitmanArmUpDown
}

one sig PitmanArmUpDown {
  , var pitmanArmUpDownPosition: one PitmanArmUpDownPosition
  , var pitmanArmDegree: one PitmanArmDegree
}

enum Direction {
  Right, Left
}

enum PitmanArmDegree {
  Low, High
}

enum PitmanArmUpDownPosition {
  Downward, Upward
}

enum PitmanArmForthBack {
  Backward, Forward
}

enum BrightnessState {
  LowBrightness, MediumBrightness, HighBrightness
}

enum BreakState {
  NeutralBreak, Break, FullBreak
}

enum LightRotarySwitch {
  Off, Auto, On
}

enum KeyState {
  NoKeyInserted, KeyInserted, KeyInIgnitionOnPosition
}

enum MarketCode {
  NorthAmerica, Other
}

enum DriverPosition {
  LeftHandDrive, RightHandDrive
}
