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
  , voltageBattery: one Level

  // Boolean attributes

  , hazardWarning: lone Yes
  , daytimeLights: lone Yes
  , ambientLighting: lone Yes

  , closedDoors: lone Yes
  , oncommingTraffic: lone Yes
  , reverseGear: lone Yes
  , cameraReady: lone Yes
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

// ----------------------------------------------------------------------------
// Initial Configuration
// ----------------------------------------------------------------------------

fact Init {
  Vehicle.keyState          = NoKeyInserted
  Vehicle.currentSpeed      = Low
  Vehicle.brakePedal        = Low
  Vehicle.voltageBattery    = Medium
  Vehicle.lightRotarySwitch = Off

  no Vehicle.hazardWarning
  no Vehicle.closedDoors
  no ArmoredVehicle.darknessMode
  no pitmanArmForthBack
  no pitmanArmUpDown
  no reverseGear
  no oncommingTraffic
  some cameraReady

  no Actuator
}

run test {}
