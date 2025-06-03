firrtl.circuit "SyncReset" {
  firrtl.module private @WhenCounter(in %clock1: !firrtl.clock, in %reset1: !firrtl.reset, out %io: !firrtl.bundle<cnt: uint<8>, tick: uint<1>>) {
    %cntReg = firrtl.regreset %clock1, %reset1, %c0_ui8 : !firrtl.clock, !firrtl.reset, !firrtl.uint<8>, !firrtl.uint<8>
  firrtl.module @SyncReset(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<value: uint<8>>) attributes {convention = #firrtl<convention scalarized>} {
    %syncReset_REG = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
    %syncReset = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
    %cnt_clock1, %cnt_reset1, %cnt_io = firrtl.instance cnt @WhenCounter(in clock1: !firrtl.clock, in reset1: !firrtl.reset, out io: !firrtl.bundle<cnt: uint<8>, tick: uint<1>>)
