firrtl.circuit "VcdAdder" {
  firrtl.module private @DoAdd(in %clock1: !firrtl.clock, in %a: !firrtl.sint<8>, in %b: !firrtl.sint<8>, out %c: !firrtl.sint<10>) {
    %accum = firrtl.reg %clock1 : !firrtl.clock, !firrtl.sint<9>
  firrtl.module @VcdAdder(in %clock: !firrtl.clock, in %io_a: !firrtl.sint<8>, in %io_b: !firrtl.sint<8>, out %io_c: !firrtl.sint<10>) attributes {convention = #firrtl<convention scalarized>} {
    %do_add_clock1, %do_add_a, %do_add_b, %do_add_c = firrtl.instance do_add @DoAdd(in clock1: !firrtl.clock, in a: !firrtl.sint<8>, in b: !firrtl.sint<8>, out c: !firrtl.sint<10>)
