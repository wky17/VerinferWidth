firrtl.circuit "TrueDualPortMemory" {
  firrtl.module @TrueDualPortMemory(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<addrA flip: uint<10>, rdDataA: uint<8>, wrEnaA flip: uint<1>, wrDataA flip: uint<8>, addrB flip: uint<10>, rdDataB: uint<8>, wrEnaB flip: uint<1>, wrDataB flip: uint<8>>) attributes {convention = #firrtl<convention scalarized>} {
