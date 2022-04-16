module properties/directionblinking

open structure/structure

// ELS-1 | Direction blinking left: When moving the pitman arm in position ”turn
// left” 3 , the vehicle flashes all left direction indicators 
// (front left, exterior mirror left, rear left) synchronously with pulse ratio bright to
// dark 1:1 and a frequency of 1.0 Hz ± 0.1 Hz (i.e. 60 flashes per minute
// ± 6 flashes).

check ELS1{
    PitmanArm . pitmanArmUpDown . pitmanArmUpDownPosition = Downward
    => eventually (some BlinkLeft)
}

// ELS-2 | Tip-blinking left: If the driver moves the pitman arm for less than 0.5
// seconds in position ”Tip-blinking left”, all left direction indicators (see
// Req. ELS-1) should flash for three flashing cycles.
check ELS2 {
    tipBlinkingLeft
    => eventually (
        highBlinkLeft and after LowBlinkLeft and after
        highBlinkLeft and after LowBlinkLeft and after
        highBlinkLeft and after LowBlinkLeft)
}


// ELS-3 | If the driver activates the pitman arm in another direction or activates
// the hazard warning light switch during the three flashing cycles of the
// tip-blinking, the tip-blinking cycle must be stopped and the requested
// flashing cycle must be started (i.e. direction blinking, tip-blinking, or
// hazard warning light, depending on the interrupting request)
check ELS3 {
    (   highBlinkLeft and 
        PitmanArm . pitmanArmUpDown . pitmanArmUpDownPosition = Upward
        => eventually (some BlinkRight and no BlinkLeft) )
    or
    (   highBlinkRight and 
        PitmanArm . pitmanArmUpDown . pitmanArmUpDownPosition = Downward
        => eventually (some BlinkLeft and no BlinkRight) )
    or
    (   (highBlinkRight or highBlinkLeft) and
        some hazardWarning
        => eventually (some hazardWarning and not (highBlinkLeft and highBlinkLeft) ) )
}


// ELS-4 | If the driver holds the pitman arm for more than 0.5 seconds in position ”tip-blinking left”, flashing cycles are initiated for all direction
// indicators on the left (see Req. ELS-1) until the pitman arm leaves the
// position ”tip-blinking left”.
check ELS4 {
    
}

// ELS-5 | Direction blinking right and tip-blinking right: Analogous to the left
// side (see Req. Req. ELS-1 to Req. ELS-4).
check ELS5 {
    PitmanArm . pitmanArmUpDown . pitmanArmUpDownPosition = Upward
    => eventually (some BlinkRight)

    tipBlinkingRight
    => eventually (
        highBlinkRight and after LowBlinkRight and after
        highBlinkRight and after LowBlinkRight and after
        highBlinkRight and after LowBlinkRight)
}

// ELS-6 | For cars sold in USA and Canada, the daytime running light must be
// dimmed by 50% during direction blinking on the blinking side.
check ELS6 {
    (Vehicle . marketCode = NorthAmerica and some daytimeLights)
    =>  (some BlinkLeft => LowBeamLeft . level = Medium)
    and (some BlinkRight => LowBeamRight . level = Medium)
}

// ELS-7 | If the driver activates the pitman arm during the three flashing cycles
// of tip-blinking for the same direction again, only the current flashing
// cycle is completed and then the new command is processed (either
// three flashing cycles due to tip-blinking or constant direction blinking).
check ELS7 {
    
}