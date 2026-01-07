firrtl.circuit "DownCounter" {
  firrtl.module @DownCounter(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<cnt: uint<8>, tick: uint<1>>) attributes {convention = #firrtl<convention scalarized>} {
    %cntReg = firrtl.regreset %clock, %reset1, %c9_ui4 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>
