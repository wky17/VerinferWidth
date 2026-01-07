firrtl.circuit "Sequential" {
  firrtl.module @Sequential(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<d flip: uint<4>, q: uint<4>, d2 flip: uint<4>, q2: uint<4>, d3 flip: uint<4>, q3: uint<4>, ena flip: uint<1>, q4: uint<4>, q5: uint<4>, q6: uint<4>, q7: uint<4>, riseIn flip: uint<1>, riseOut: uint<1>>) attributes {convention = #firrtl<convention scalarized>} {
    %q = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<4>
    %delayReg = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<4>
    %valReg = firrtl.regreset %clock, %reset1, %c0_ui4 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>
    %enableReg = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<4>
    %resetEnableReg = firrtl.regreset %clock, %reset1, %c0_ui4 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>
    %enableReg2 = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<4>
    %resetEnableReg2 = firrtl.regreset %clock, %reset1, %c0_ui4 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>
    %risingEdge_REG = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
    %risingEdge = firrtl.node %18 : !firrtl.uint<1>
