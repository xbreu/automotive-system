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
  , highBeamHighRange: lone Yes
  , highBeamHighMotor: lone Yes
}

// ----------------------------------------------------------------------------
// Vehicle
// ----------------------------------------------------------------------------

one sig Vehicle {
  // Car attributes
  , driverHand: one HorizontalDirection
  , marketCode: one MarketCode

  // User interface
  , lightRotarySwitch: one SwitchState
  , hazardWarning: lone Yes
  , daytimeLights: lone Yes
  , ambientLighting: lone Yes

  // Sensors
  , keyState: one KeyState
  , brightnessSensor: one Level
  , brakePedal: one Level
  , voltageBattery: one Level
  , closedDoors: lone Yes
  , oncommingTraffic: lone Yes
  , cameraReady: lone Yes
  , currentSpeed: one Level
  , reverseGear: lone Yes
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
// Predicates
// ----------------------------------------------------------------------------

pred highBlinkLeft {
  some BlinkLeft and BlinkLeft . level = High
}

pred highBlinkRight {
  some BlinkRight and BlinkRight . level = High
}

pred parkingLight {
  some LowBeamLeft and some LowBeamRight
  some TailLampLeft and some TailLampRight
  LowBeamLeft . level & LowBeamRight . level = Low
  TailLampLeft . level & TailLampRight . level = Low
}

// ----------------------------------------------------------------------------
// Initial Configuration
// ----------------------------------------------------------------------------

fact Init {
  /*
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
  no ActuatorWithLevel
  */
}
