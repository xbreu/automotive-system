module visualization

open structure/structure

// ----------------------------------------------------------------------------
// Aggregator Signatures
// ----------------------------------------------------------------------------

abstract sig System {
  , var component: univ
}

one sig SensorSystem
      , ActuatorSystem
extends System {}

fact {
  SensorSystem . component = DummySensor
  ActuatorSystem . component = DummyActuator
}

// ----------------------------------------------------------------------------
// Actuators
// ----------------------------------------------------------------------------

var sig DummyActuator {}

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
  one (ActiveBlinkLeft + InactiveBlinkLeft)
  one (ActiveBlinkRight + InactiveBlinkRight)
  one (ActiveLowBeamLeft + InactiveLowBeamLeft)
  one (ActiveLowBeamRight + InactiveLowBeamRight)
  one (ActiveCorneringLightLeft + InactiveCorneringLightLeft)
  one (ActiveCorneringLightRight + InactiveCorneringLightRight)
  one (ActiveBrakeLight + InactiveBrakeLight)
  one (ActiveTailLampLeft + InactiveTailLampLeft)
  one (ActiveTailLampRight + InactiveTailLampRight)
  one (ActiveReverseLight + InactiveReverseLight)

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

// ----------------------------------------------------------------------------
// Sensors
// ----------------------------------------------------------------------------

var sig DummySensor {}

// TODO: Add steering wheel angle
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
  one (NoKey + KeyInIgnition)
  one (EngineOn + EngineOff)
  one (LowBrightness + MediumBrightness + HighBrightness)
  one (NeutralBrakePedal + DeflectedBrakePedal + VeryDeflectedBrakePedal)
  one (LowVoltageBattery + MediumVoltageBattery + HighVoltageBattery)
  one (AllDoorsClosed + SomeOpenDoor)
  one (OncommingTraffic + NoOncommingTraffic)
  one (NotReadyCamera + ReadyCamera)
  one (LowSpeed + MediumSpeed + HighSpeed)
  one (ReverseGear + ForwardGear)

  Vehicle . keyState = NoKeyInserted <=> some NoKey
  Vehicle . keyState = KeyInIgnitionOnPosition <=> some EngineOn
  Vehicle . brightnessSensor = Low <=> some LowBrightness
  Vehicle . brightnessSensor = High <=> some HighBrightness
  Vehicle . brakePedal = Low <=> some NeutralBrakePedal
  Vehicle . brakePedal = High <=> some VeryDeflectedBrakePedal
  Vehicle . voltageBattery = Low <=> some LowVoltageBattery
  Vehicle . voltageBattery = High <=> some HighVoltageBattery
  some ClosedDoorsVehicle <=> some AllDoorsClosed
  some OncommingTrafficVehicle <=> some OncommingTraffic
  some CameraReadyVehicle <=> some ReadyCamera
  Vehicle . currentSpeed = Low <=> some LowSpeed
  Vehicle . currentSpeed = High <=> some HighSpeed
  some ReverseGearVehicle <=> some ReverseGear
}
