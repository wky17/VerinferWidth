firrtl.circuit "ByteEnableMemory" {
  firrtl.module @ByteEnableMemory(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<readAddr flip: uint<16>, dataOut: vector<uint<8>, 2>, readEnable flip: uint<1>, dataIn flip: vector<uint<8>, 2>, writeAddr flip: uint<16>, writeMask flip: vector<uint<1>, 2>>) attributes {convention = #firrtl<convention scalarized>} {
