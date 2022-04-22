module visualization

open structure/structure
open util/boolean

// ----------------------------------------------------------------------------
// Aggregator Signatures
// ----------------------------------------------------------------------------

abstract sig System {
  , var component: set DummyElement
}

abstract sig DummyElement {}

one sig SensorSystem
      , ActuatorSystem
extends System {}

fact {
  always {
    component in (SensorSystem -> DummySensor + ActuatorSystem -> DummyActuator)
  }
}

// ----------------------------------------------------------------------------
// Actuators
// ----------------------------------------------------------------------------

abstract sig DummyActuator extends DummyElement {}

one sig ActiveBlinkLeft
      , InactiveBlinkLeft
      , ActiveBlinkRight
      , InactiveBlinkRight
      , ActiveLowBeamLeft
      , InactiveLowBeamLeft
      , ActiveLowBeamRight
      , InactiveLowBeamRight
      , InactiveHighBeam
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

one sig ActiveHighBeam
extends DummyActuator {
  , highRange: one Bool
  , highMotor: one Bool
}

fact {
  always {
    one component . (ActiveBlinkLeft + InactiveBlinkLeft)
    one component . (ActiveBlinkRight + InactiveBlinkRight)
    one component . (ActiveLowBeamLeft + InactiveHighBeam)
    one component . (ActiveHighBeam + InactiveLowBeamLeft)
    one component . (ActiveLowBeamRight + InactiveLowBeamRight)
    one component . (ActiveCorneringLightLeft + InactiveCorneringLightLeft)
    one component . (ActiveCorneringLightRight + InactiveCorneringLightRight)
    one component . (ActiveBrakeLight + InactiveBrakeLight)
    one component . (ActiveTailLampLeft + InactiveTailLampLeft)
    one component . (ActiveTailLampRight + InactiveTailLampRight)
    one component . (ActiveReverseLight + InactiveReverseLight)

    some BlinkLeft <=> some component . ActiveBlinkLeft
    some BlinkRight <=> some component . ActiveBlinkRight
    some LowBeamLeft <=> some component . ActiveLowBeamLeft
    some LowBeamRight <=> some component . ActiveLowBeamRight
    some HighBeam <=> some component . ActiveHighBeam
    some CorneringLightLeft <=> some component . ActiveCorneringLightLeft
    some CorneringLightRight <=> some component . ActiveCorneringLightRight
    some BrakeLight <=> some component . ActiveBrakeLight
    some TailLampLeft <=> some component . ActiveTailLampLeft
    some TailLampRight <=> some component . ActiveTailLampRight
    some ReverseLight <=> some component . ActiveReverseLight

    some HighRangeHighBeam <=> ActiveHighBeam . highRange = True
    some HighMotorHighBeam <=> ActiveHighBeam . highMotor = True
  }
}

// ----------------------------------------------------------------------------
// Sensors
// ----------------------------------------------------------------------------

abstract sig DummySensor extends DummyElement {}

one sig NoKey
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
    one component . (NoKey + KeyInIgnition)
    one component . (EngineOn + EngineOff)
    one component . (AllDoorsClosed + SomeOpenDoor)
    one component . (OncommingTraffic + NoOncommingTraffic)
    one component . (NotReadyCamera + ReadyCamera)
    one component . (ReverseGear + ForwardGear)


    Vehicle . keyState = NoKeyInserted <=> some component . NoKey
    Vehicle . keyState = KeyInIgnitionOnPosition <=> some component . EngineOn
    Vehicle . brightnessSensor = Low <=> some component . LowBrightness
    Vehicle . brightnessSensor = Medium <=> some component . MediumBrightness
    Vehicle . brightnessSensor = High <=> some component . HighBrightness
    Vehicle . brakePedal = Low <=> some component . NeutralBrakePedal
    Vehicle . brakePedal = Medium <=> some component . DeflectedBrakePedal
    Vehicle . brakePedal = High <=> some component . VeryDeflectedBrakePedal
    some SteeringLeft <=> some component . LeftSteeringWheel
    no SteeringWheel <=> some component . NeutralSteeringWheel
    some SteeringRight <=> some component . RightSteeringWheel
    Vehicle . voltageBattery = Low <=> some component . LowVoltageBattery
    Vehicle . voltageBattery = Medium <=> some component . MediumVoltageBattery
    Vehicle . voltageBattery = High <=> some component . HighVoltageBattery
    some ClosedDoorsVehicle <=> some component . AllDoorsClosed
    some OncommingTrafficVehicle <=> some component . OncommingTraffic
    some CameraReadyVehicle <=> some component . ReadyCamera
    Vehicle . currentSpeed = Low <=> some component . LowSpeed
    Vehicle . currentSpeed = Medium <=> some component . MediumSpeed
    Vehicle . currentSpeed = High <=> some component . HighSpeed
    some ReverseGearVehicle <=> some component . ReverseGear
  }
}

// ----------------------------------------------------------------------------
// User Interface
// ----------------------------------------------------------------------------
