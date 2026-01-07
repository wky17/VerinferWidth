firrtl.circuit "Conditional" {
  firrtl.module @Conditional(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<condition flip: uint<1>, result: uint<4>>) attributes {convention = #firrtl<convention scalarized>} {
    %c1 = firrtl.node %2 : !firrtl.uint<1>
    %c2 = firrtl.node %2 : !firrtl.uint<1>
    %v = firrtl.wire : !firrtl.uint<3>
