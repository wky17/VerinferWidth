firrtl.circuit "ShouldBeBadUIntSubtractWithGrow" {
  firrtl.module @ShouldBeBadUIntSubtractWithGrow(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<a flip: uint<4>, b flip: uint<4>, o: uint<4>>) attributes {convention = #firrtl<convention scalarized>} {
    %r = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<4>
