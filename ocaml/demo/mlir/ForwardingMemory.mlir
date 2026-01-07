firrtl.circuit "ForwardingMemory" {
  firrtl.module @ForwardingMemory(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<rdAddr flip: uint<10>, rdData: uint<8>, wrAddr flip: uint<10>, wrData flip: uint<8>, wrEna flip: uint<1>>) attributes {convention = #firrtl<convention scalarized>} {
    %wrDataReg = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<8>
    %doForwardReg = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
