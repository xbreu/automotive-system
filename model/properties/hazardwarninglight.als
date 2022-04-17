module properties/hazardwarninglight

open structure/structure

// ELS-8 | As long as the hazard warning light switch is pressed (active), all
// direction indicators flash synchronously. If the ignition key is in the
// ignition lock, the pulse ratio is bright to dark 1:1. If the ignition key is
// not in the lock, the pulse ratio is 1:2.
check ELS8 {

}

// ELS-9 | The adaptation of the pulse ratio must occur at the latest after two
// complete flashing cycles.
// Note: The reduction of the pulse is performed due to energy saving reasons,
// such that, in case of an emergency situation, the hazard warning light is
// active as long as possible before the car battery is empty.
check ELS9 {

}

// ELS-10 | The duration of a flashing cycle is 1 second.
check ELS10 {
  // The time was abstracted in a way that leaves us without a way of checking
  // this specific system property.
}

// ELS-11 | A flashing cycle (bright to dark) must always be completed, before
// a new flashing cycle can occur.
// Note: By the fact, that a flashing cycle must always be completed, a
// "switching" behavior of the indicator is avoided. Thus, for example a change
// of the pitman arm from "tip-blinking" to "direction blinking" or back has no
// visible effect.
check ELS11 {

}

// ELS-12 | When hazard warning is deactivated again, the pitman arm is in
// position "direction blinking left" or "direction blinking right" ignition is
// On, the direction blinking cycle should be started (see Req. ELS-1).
check ELS12 {
  always (
    ((some hazardWarning);
     (no hazardWarning and directionBlinking and engineOn))
    => always after directionBlinking => (
      eventually some Blink and eventually no Blink
    )
  )
}

// ELS-13 | If the warning light is activated, any tip-blinking will be ignored
// or stopped if it was started before.
check ELS13 {
  always (
    some hazardWarning => no Blink
  )
}
