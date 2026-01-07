firrtl.circuit "GCD" {
  firrtl.module @GCD(in %clk: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<a flip: uint<16>, b flip: uint<16>, e flip: uint<1>, z: uint<16>, v: uint<1>>) attributes {convention = #firrtl<convention scalarized>} {
    %x = firrtl.reg %clk : !firrtl.clock, !firrtl.uint<16>
    %y = firrtl.reg %clk : !firrtl.clock, !firrtl.uint<16>
    %T_7 = firrtl.node %5 : !firrtl.uint<1>
      %T_8 = firrtl.node %9 : !firrtl.uint<17>
      %T_9 = firrtl.node %10 : !firrtl.uint<16>
    %T_10 = firrtl.node %5 : !firrtl.uint<1>
    %T_12 = firrtl.node %6 : !firrtl.uint<1>
      %T_13 = firrtl.node %9 : !firrtl.uint<17>
      %T_14 = firrtl.node %10 : !firrtl.uint<16>
    %T_16 = firrtl.node %8 : !firrtl.uint<1>
