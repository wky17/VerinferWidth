firrtl.circuit "Example" {
  firrtl.module @Example(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %in: !firrtl.uint<2>, out %out: !firrtl.uint<2>) attributes {convention = #firrtl<convention scalarized>} {
