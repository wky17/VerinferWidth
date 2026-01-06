circuit Foo :
  module Foo :
    input in : UInt<2>
    input clock : Clock

    reg x0 : UInt, clock
    reg x1 : UInt, clock
    reg x2 : UInt, clock
    reg x3 : UInt, clock
    reg x4 : UInt, clock

    connect x0, shl(x1,1) @"x(0,0) >= 1*x(1,0) + 1",
    connect x1, cat(x4,tail(x4,1)) @"x(1,0) >= 2*x(4,0) + -1",
    connect x2, mul(cat(x3,shl(x3,3)),x3) @"x(2,0) >= 3*x(3,0) + 3",
    connect x3, shr(UInt<0>(0),5) @"x(3,0) >= 0*x(0,0) + -5",
    connect x4, tail(x2,2) @"x(4,0) >= 1*x(2,0) + -2",
    connect x0, mul(x4,x3) @"x(0,0) >= 1*x(3,0) + 1*x(4,0)",
    connect x2, cat (x1, x4) @"x(2,0) >= 1*x(1,0) + 1*x(4,0)"
    