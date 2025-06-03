circuit Foo :
  module Foo :
    input in : UInt<2>
    input clock : Clock

    reg x0 : UInt, clock
    reg x1 : UInt, clock
    reg x2 : UInt, clock
    reg x3 : UInt, clock

    connect x0, shr(mul(cat(mul(x1,x2), cat(x2,x1)),x1), 4) @"x(0,0) >= 3*x(1,0) + 2*x(2,0) + -4",
    connect x2, shl(x3, 1) @"x(2,0) >= 1*x(3,0) + 1",
    connect x1, cat(x2, shr(x2,2)) @"x(1,0) >= 2*x(2,0) + -2",
    connect x3, tail(x0,5) @"x(3,0) >= 1*x(0,0) + -5"
