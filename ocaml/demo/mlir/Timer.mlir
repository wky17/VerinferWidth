firrtl.circuit "Timer" {
  firrtl.module @Timer(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<din flip: uint<8>, load flip: uint<1>, done: uint<1>>) attributes {convention = #firrtl<convention scalarized>} {
    %cntReg = firrtl.regreset %clock, %reset1, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
    %done = firrtl.node %3 : !firrtl.uint<1>
    %next = firrtl.wire : !firrtl.uint<8>
