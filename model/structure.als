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
// Facts
// ----------------------------------------------------------------------------

/*
Control of the low beam headlights. If daytime running light is activated, low beam headlights are active all the time and
ambient light illuminates the vehicle surrounding while leaving the car during
darkness.The function low beam headlight also includes parking light.
*/
fact {
  some daytimeLights => some LowBeamLeft and some LowBeamRight
}

// Direction blinking is only available when the ignition is on
fact {
  (blinkLeft or blinkRight) => Vehicle . keyState = KeyInIgnitionOnPosition
}

// ELS-6 For cars sold in USA and Canada, the daytime running light must be
// dimmed by 50% during direction blinking on the blinking side

fact {
  (Vehicle . marketCode = NorthAmerica and blinkLeft) => LowBeamLeft . level = Medium
  (Vehicle . marketCode = NorthAmerica and blinkRight) => LowBeamRight . level = Medium
}

// ELS-14 If the ignition is On and the light rotary switch is in the position On,
// then low beam headlights are activated.
fact {
  (Vehicle . keyState = KeyInIgnitionOnPosition and 
   Vehicle . lightRotarySwitch = On) => some LowBeamLeft and some LowBeamRight
}

// ELS-21 With activated darkness switch (only armored vehicles) the ambient
// lighting is not activated.

fact {
  some Vehicle . darknessMode => no Vehicle . ambientLighting
}

// ELS-22 Whenever the low or high beam headlights are activated, the tail
// lights are activated, too.
fact {
  some LowBeamLeft + LowBeamRight + HighBeam => some TailLampLeft and some TailLampRight
}

// ELS-41 The reverse light is activated whenever the reverse gear is engaged.
fact {
  some Vehicle . reverseGear => some ReverseLight
}

// ----------------------------------------------------------------------------
// Predicates
// ----------------------------------------------------------------------------

pred blinkLeft {
  some BlinkLeft and BlinkLeft . level = High
}

pred blinkRight {
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

run test {}
