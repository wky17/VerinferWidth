firrtl.circuit "Bar" {
  firrtl.module @Bar(in %clock: !firrtl.clock, in %cond: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
    %a = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<2>
    %false = firrtl.node %2 : !firrtl.uint<2>
