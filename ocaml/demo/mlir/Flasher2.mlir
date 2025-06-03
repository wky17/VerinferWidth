firrtl.circuit "Flasher2" {
  firrtl.module @Flasher2(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<start flip: uint<1>, light: uint<1>>) attributes {convention = #firrtl<convention scalarized>} {
    %start = firrtl.node %2 : !firrtl.uint<1>
    %stateReg = firrtl.regreset %clock, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<2>
    %light = firrtl.wire : !firrtl.uint<1>
    %timerLoad = firrtl.wire : !firrtl.uint<1>
    %timerSelect = firrtl.wire : !firrtl.uint<1>
    %timerDone = firrtl.wire : !firrtl.uint<1>
    %cntLoad = firrtl.wire : !firrtl.uint<1>
    %cntDecr = firrtl.wire : !firrtl.uint<1>
    %cntDone = firrtl.wire : !firrtl.uint<1>
    %cntReg = firrtl.regreset %clock, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<2>
    %timerReg = firrtl.regreset %clock, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<3>
