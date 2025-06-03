firrtl.circuit "Foo" {
  firrtl.module @Foo() attributes {convention = #firrtl<convention scalarized>} {
    %a = firrtl.node %c42_ui6 : !firrtl.uint<6>
    %b = firrtl.node %c42_ui6_0 : !firrtl.uint<6>
    %c = firrtl.node %c42_ui6_0 : !firrtl.uint<6>
    %d = firrtl.node %c42_ui6 : !firrtl.uint<6>
    %e = firrtl.node %c42_ui6 : !firrtl.uint<6>
