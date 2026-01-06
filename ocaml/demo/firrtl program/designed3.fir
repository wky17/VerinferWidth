circuit Foo :
  module Foo :
    input in : UInt<4>
    input clock : Clock
    output out : UInt

    reg x1 : UInt, clock
    reg x2 : UInt, clock
    reg x3 : UInt, clock

    connect x1, shl(mul(x3, mul(x2, x2)), 1) @x(0,0) ≥ 2*x(1,0) + 1*x(2,0) + 1
    connect x3, shr(mul(x2, mul(x2,x2)),2) @x(2,0) ≥ 3*x(1,0) + -2
    connect x2, shr(x1,3)
    connect out, mux(cat(x1, cat(x3,x3)),x1,x1)
    connect out, mux(cat(x2, cat(x3,cat(x3,x3))),x1,x1)
