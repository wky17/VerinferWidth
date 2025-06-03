circuit Foo :
  module Foo :
    input in : UInt<2>
    input clock : Clock

    reg x0 : UInt, clock
    reg x1 : UInt, clock
    reg x2 : UInt, clock
    reg x3 : UInt, clock
    reg x4 : UInt, clock

    connect x0, tail(mul(cat(x1,x2), x1), 4) @"x(0,0) >= 2*x(1,0) + 1*x(2,0) + -4",
    connect x2, shl(x4, 1) @"x(2,0) >= 1*x(4,0) + 1",
    connect x1, tail(mul(cat(x3,x3), x3), 2) @"x(1,0) >= 3*x(3,0) + -2",
    connect x3, tail(x4, 1) @"x(3,0) >= 1*x(4,0) + -1",
    connect x4, tail(x0, 3) @"x(4,0) >= 1*x(0,0) + -3"
    