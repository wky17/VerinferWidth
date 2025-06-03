circuit Foo :
  module Foo :
    input in : UInt<2>
    input clock : Clock

    reg x0 : UInt, clock
    reg x1 : UInt, clock
    reg x2 : UInt, clock
    reg x3 : UInt, clock
    reg x4 : UInt, clock
    reg x5 : UInt, clock

    connect x0, shl(x1,2) @"x(0,0) >= 1*x(1,0) + 2",
    connect x1, cat(x4,tail(x4,1)) @"x(1,0) >= 2*x(4,0) + -1",
    connect x2, mul(x5,x3) @"x(2,0) >= 1*x(3,0) + 1*x(5,0)",
    connect x3, shr(x2,2) @"x(3,0) >= 1*x(2,0) + -2",
    connect x4, tail(x0,2) @"x(4,0) >= 1*x(0,0) + -2",
    connect x5, shr(UInt<0>(0),3) @"x(5,0) >= 0*x(4,0) + -3",
    connect x1, cat (x5, UInt<1>(0)) @"x(1,0) >= 1*x(5,0) + 1"
    