circuit Foo :
  module Foo :
    input in : UInt<2>
    input clock : Clock

    reg x0 : UInt, clock
    reg x1 : UInt, clock
    reg x2 : UInt, clock

    connect x0, shr(mul(cat(mul(x1,x2), cat(x2,x1)),x2), 1) @"x(0,0) >= 2*x(1,0) + 3*x(2,0) + -1",
    connect x1, shl(x2,1) @"x(1,0) >= 1*x(2,0) + 1",
    connect x2, shr(x0, 3) @"x(2,0) >= 1*x(0,0) + -3"
