firrtl.circuit "MultiClockSubModuleTest" {
  firrtl.module private @MultiClockSubModuleTestSubModule(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<out_wky: uint<4>>) {
    %value = firrtl.regreset %clock1, %reset1, %c0_ui4 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>
  firrtl.module @MultiClockSubModuleTest(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<>) attributes {convention = #firrtl<convention scalarized>} {
    %value = firrtl.regreset %clock, %reset1, %c0_ui4 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>
    %done = firrtl.node %2 : !firrtl.uint<1>
    %cDiv = firrtl.regreset %clock, %reset1, %c1_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>
    %otherClock = firrtl.node %5 : !firrtl.clock
    %otherReset = firrtl.node %6 : !firrtl.uint<1>
    %inst1_clock1, %inst1_reset1, %inst1_io = firrtl.instance inst1 @MultiClockSubModuleTestSubModule(in clock1: !firrtl.clock, in reset1: !firrtl.uint<1>, out io: !firrtl.bundle<out_wky: uint<4>>)
