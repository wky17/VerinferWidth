firrtl.circuit "Widths" {
  firrtl.module @Widths(in %x: !firrtl.uint<1>, in %y: !firrtl.uint<2>, out %out1: !firrtl.uint<2>, out %out2: !firrtl.uint<2>) attributes {convention = #firrtl<convention scalarized>} {
    %w = firrtl.wire : !firrtl.uint<2>
    %wx = firrtl.wire : !firrtl.uint<2>
