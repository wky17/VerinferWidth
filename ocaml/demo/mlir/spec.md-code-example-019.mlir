firrtl.circuit "Foo" {
  firrtl.module @Foo() attributes {convention = #firrtl<convention scalarized>} {
    %v = firrtl.wire : !firrtl.vector<uint<6>, 3>
