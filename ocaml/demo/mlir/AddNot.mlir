firrtl.circuit "Foo" {
  firrtl.module @Foo(in %b: !firrtl.uint<1>, out %a: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
