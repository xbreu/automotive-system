module interface

one sig Yes {}

one sig Vehicle {
  // Enumeration attributes
  , driverPosition: one DriverPosition
  , marketCode: one MarketCode
  , var keyState: one KeyState
  , var cameraState: one CameraState
  , var lightRotarySwitch: one LightRotarySwitch

  // Numerical attributes
  , var currentSpeed: one Int
  , var brightnessSensor: one Int
  , var brakePedal: one Int
  , var voltageBattery: one Int
  , var steeringAngle: one Int

  // Boolean attributes
  , var hazardWarning: lone Yes
  , var engineOn: lone Yes
  , var closedDoors: lone Yes
  , var oncommingTraffic: lone Yes
  , var reverseGear: lone Yes

  // Sig attributes
  , pitmanArm: one PitmanArm
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

enum PitmanArmDegree {
  Degree5, Degree7
}

enum PitmanArmUpDownPosition {
  Downward, Upward
}

enum PitmanArmForthBack {
  Backward, Forward
}

enum KeyState {
  NoKeyInserted, KeyInserted, KeyInIgnitionOnPosition
}

enum CameraState {
  Ready, Dirty, NotReady
}

enum LightRotarySwitch {
  Off, Auto, On
}

enum DriverPosition {
  LeftHandDrive, RightHandDrive
}

enum MarketCode {
  USA, Canada, EU
}

run Example {}
