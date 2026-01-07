firrtl.circuit "OverflowTypeCircuit" {
  firrtl.module @OverflowTypeCircuit(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<a flip: sint<4>, b flip: sint<4>, addWrap: sint<5>, addGrow: sint<5>, subWrap: sint<5>, subGrow: sint<5>>) attributes {convention = #firrtl<convention scalarized>} {
    %regAddWrap = firrtl.reg %clock : !firrtl.clock, !firrtl.sint<4>
    %regAddGrow = firrtl.reg %clock : !firrtl.clock, !firrtl.sint<5>
    %regSubWrap = firrtl.reg %clock : !firrtl.clock, !firrtl.sint<4>
    %regSubGrow = firrtl.reg %clock : !firrtl.clock, !firrtl.sint<5>
