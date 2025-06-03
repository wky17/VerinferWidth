circuit Foo :
  module Foo :
    input in : UInt<2>
    input clock : Clock

    reg x0 : UInt, clock
    reg x1 : UInt, clock
    reg x2 : UInt, clock
    reg x3 : UInt, clock

    connect x0, shr(mul(cat(mul(x1,x3), cat(x3,x1)),x3), 1) @"x(0,0) >= 2*x(1,0) + 3*x(3,0) + -1",
    connect x1, shl(x2,1) @"x(1,0) >= 1*x(2,0) + 1",
    connect x2, tail(x3,3) @"x(2,0) >= 1*x(3,0) + -3",
    connect x3, mul(tail(x0,4), x0) @"x(3,0) >= 2*x(0,0) + -4"
