firrtl.circuit "Foo" {
  firrtl.module @Foo() attributes {convention = #firrtl<convention scalarized>} {
    %a = firrtl.node %c-42_si7 : !firrtl.sint<7>
    %b = firrtl.node %c-42_si7_0 : !firrtl.sint<7>
    %c = firrtl.node %c-42_si7_0 : !firrtl.sint<7>
    %d = firrtl.node %c-42_si7 : !firrtl.sint<7>
    %e = firrtl.node %c-42_si7 : !firrtl.sint<7>
