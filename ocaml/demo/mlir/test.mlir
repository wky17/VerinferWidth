firrtl.circuit "Foo" {
  firrtl.module @Foo(in %clock: !firrtl.clock, out %io: !firrtl.uint<10>) attributes {convention = #firrtl<convention scalarized>} {
    %a1 = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
