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
    Up,
    Down
}

enum HorizontalDirection {
    Forth,
    Back
}

sig Direction {
    vertical: one VerticalDirection,
    horizontal: one HorizontalDirection
}

one sig PitmanArm {
    direction: one Direction
}
