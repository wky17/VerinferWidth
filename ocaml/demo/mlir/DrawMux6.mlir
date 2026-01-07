firrtl.circuit "DrawMux6" {
  firrtl.module @DrawMux6(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<sel flip: uint<3>, dout: uint<8>>) attributes {convention = #firrtl<convention scalarized>} {
    %dout = firrtl.wire : !firrtl.uint<6>
