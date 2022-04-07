module sensors

open arquitecture as a

// ----------------------------------------------------------------------------
// Definitions
// ----------------------------------------------------------------------------

enum KeyState {
    NoKeyInserted,
    KeyInserted,
    KeyInIgnitionOnPosition
}

let BrightnessLevel = {
	level : Int | level >= 0 and level <= 100000 
}

