circuit Foo :
  module Foo :
    input in : UInt<2>
    input clock : Clock

    reg x0 : UInt, clock
    reg x1 : UInt, clock
    reg x2 : UInt, clock

    connect x0, shl(x2,2) @x(0,0) ≥ 1*x(2,0) + 2",
    connect x1, mul(x0, x2) @"x(1,0) ≥ 1*x(0,0) + 1*x(2,0)",
    connect x2, shr(x1,3) @"x(2,0) ≥ 1*x(1,0) + -3"
