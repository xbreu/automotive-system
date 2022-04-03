module interface

open arquitecture as a

// ----------------------------------------------------------------------------
// Definitions
// ----------------------------------------------------------------------------

enum SwitchOptions {
    Off,
    Auto,
    On
}

enum VerticalDirection {
    NeutralV,
    Upward5,	// 5º deflection
    Upward7,	// 7º deflection
    Downward5,
    Downward7
}

enum HorizontalDirection {
    NeutralH,
    Forth,
    Back
}

sig Direction {
    vertical: one VerticalDirection,
    horizontal: one HorizontalDirection
}

sig SwitchOn {
	switch: one Boolean
}

one sig PitmanArm {
    direction: one Direction
}

one sig LightRotarySwitch {
	switchOptions: one SwitchOptions
}

one sig HarzardWarning, DarknessMode extends SwitchOn {}





 
