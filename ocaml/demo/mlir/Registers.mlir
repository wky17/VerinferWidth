firrtl.circuit "Registers" {
  firrtl.module @Registers(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<in_wky flip: uint<8>, out_wky: uint<8>>) attributes {convention = #firrtl<convention scalarized>} {
    %q = firrtl.regreset %clock, %reset1, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
    %nextReg = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<8>
    %bothReg = firrtl.regreset %clock, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<8>
