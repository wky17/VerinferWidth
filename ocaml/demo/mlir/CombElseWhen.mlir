firrtl.circuit "CombElseWhen" {
  firrtl.module @CombElseWhen(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<cond flip: uint<1>, cond2 flip: uint<1>, out_wky: uint<4>>) attributes {convention = #firrtl<convention scalarized>} {
    %w = firrtl.wire : !firrtl.uint<2>
