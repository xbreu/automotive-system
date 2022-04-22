module visualization

open structure/structure

// ----------------------------------------------------------------------------
// Aggregator Signatures
// ----------------------------------------------------------------------------

abstract sig System {
  , var component: set univ
}

one sig SensorSystem
      , ActuatorSystem
extends System {}

fact {
  always {
    SensorSystem . component = DummySensor
    ActuatorSystem . component = DummyActuator
  }
}

// ----------------------------------------------------------------------------
// Actuators
// ----------------------------------------------------------------------------

var abstract sig DummyActuator {}

// TODO: implement high beam
var lone sig ActiveBlinkLeft
           , InactiveBlinkLeft
           , ActiveBlinkRight
           , InactiveBlinkRight
           , ActiveLowBeamLeft
           , InactiveLowBeamLeft
           , ActiveLowBeamRight
           , InactiveLowBeamRight
           , ActiveCorneringLightLeft
           , InactiveCorneringLightLeft
           , ActiveCorneringLightRight
           , InactiveCorneringLightRight
           , ActiveBrakeLight
           , InactiveBrakeLight
           , ActiveTailLampLeft
           , InactiveTailLampLeft
           , ActiveTailLampRight
           , InactiveTailLampRight
           , ActiveReverseLight
           , InactiveReverseLight
     extends DummyActuator {}

fact {
  always {
    /*one (ActiveBlinkLeft + InactiveBlinkLeft)
    one (ActiveBlinkRight + InactiveBlinkRight)
    one (ActiveLowBeamLeft + InactiveLowBeamLeft)
    one (ActiveLowBeamRight + InactiveLowBeamRight)
    one (ActiveCorneringLightLeft + InactiveCorneringLightLeft)
    one (ActiveCorneringLightRight + InactiveCorneringLightRight)
    one (ActiveBrakeLight + InactiveBrakeLight)
    one (ActiveTailLampLeft + InactiveTailLampLeft)
    one (ActiveTailLampRight + InactiveTailLampRight)
    one (ActiveReverseLight + InactiveReverseLight)*/

    some BlinkLeft <=> some ActiveBlinkLeft
    some BlinkRight <=> some ActiveBlinkRight
    some LowBeamLeft <=> some ActiveLowBeamLeft
    some LowBeamRight <=> some ActiveLowBeamRight
    some CorneringLightLeft <=> some ActiveCorneringLightLeft
    some CorneringLightRight <=> some ActiveCorneringLightRight
    some BrakeLight <=> some ActiveBrakeLight
    some TailLampLeft <=> some ActiveTailLampLeft
    some TailLampRight <=> some ActiveTailLampRight
    some ReverseLight <=> some ActiveReverseLight
  }
}

// ----------------------------------------------------------------------------
// Sensors
// ----------------------------------------------------------------------------

var abstract sig DummySensor {}

var lone sig NoKey
           , KeyInIgnition
           , EngineOn
           , EngineOff
           , LowBrightness
           , MediumBrightness
           , HighBrightness
           , NeutralBrakePedal
           , DeflectedBrakePedal
           , VeryDeflectedBrakePedal
           , LowVoltageBattery
           , MediumVoltageBattery
           , HighVoltageBattery
           , LeftSteeringWheel
           , NeutralSteeringWheel
           , RightSteeringWheel
           , AllDoorsClosed
           , SomeOpenDoor
           , OncommingTraffic
           , NoOncommingTraffic
           , NotReadyCamera
           , ReadyCamera
           , LowSpeed
           , MediumSpeed
           , HighSpeed
           , ReverseGear
           , ForwardGear
     extends DummySensor {}

fact {
  always {
    /*one (NoKey + KeyInIgnition)
    one (EngineOn + EngineOff)
    one (AllDoorsClosed + SomeOpenDoor)
    one (OncommingTraffic + NoOncommingTraffic)
    one (NotReadyCamera + ReadyCamera)
    one (LowSpeed + MediumSpeed + HighSpeed)
    one (ReverseGear + ForwardGear)*/

    Vehicle . keyState = NoKeyInserted <=> some NoKey
    Vehicle . keyState = KeyInIgnitionOnPosition <=> some EngineOn
    Vehicle . brightnessSensor = Low <=> some LowBrightness
    Vehicle . brightnessSensor = Medium <=> some MediumBrightness
    Vehicle . brightnessSensor = High <=> some HighBrightness
    Vehicle . brakePedal = Low <=> some NeutralBrakePedal
    Vehicle . brakePedal = Medium <=> some DeflectedBrakePedal
    Vehicle . brakePedal = High <=> some VeryDeflectedBrakePedal
    /*some SteeringLeft <=> some LeftSteeringWheel
    no SteeringWheel <=> some NeutralSteeringWheel
    some SteeringRight <=> some RightSteeringWheel
    Vehicle . voltageBattery = Low <=> some LowVoltageBattery
    Vehicle . voltageBattery = Medium <=> some MediumVoltageBattery
    Vehicle . voltageBattery = High <=> some HighVoltageBattery
    some ClosedDoorsVehicle <=> some AllDoorsClosed
    some OncommingTrafficVehicle <=> some OncommingTraffic
    some CameraReadyVehicle <=> some ReadyCamera
    Vehicle . currentSpeed = Low <=> some LowSpeed
    Vehicle . currentSpeed = High <=> some HighSpeed
    some ReverseGearVehicle <=> some ReverseGear*/
  }
}
