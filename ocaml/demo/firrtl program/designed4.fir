circuit Foo :
  module Foo :
    input in : UInt<2>
    input clock : Clock

    reg x0 : UInt, clock
    reg x1 : UInt, clock
    reg x2 : UInt, clock
    reg x3 : UInt<0>, clock
    reg x4 : UInt<0>, clock

    connect x0, mul(x2, mul(shl(x3,2),x3)) @x(0,0) ≥ 1*x(2,0) + 2*x(3,0) + 2",
    connect x1, mul(x0, x2) @"x(1,0) ≥ 1*x(0,0) + 1*x(2,0)",
    connect x2, mul(x4,shr(x4,1)) @"x(2,0) ≥ 2*x(4,0) + -1",
    connect x2, mul(x1, mul(x3, shr(x4,3))) @"x(2,0) ≥ 1*x(1,0) + 1*x(3,0) + 1*x(4,0) + -3"
