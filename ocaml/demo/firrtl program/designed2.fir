circuit Foo :
  module Foo :
    input in : UInt<4>
    input clock : Clock
    output out : UInt

    reg x1 : UInt, clock
    reg x2 : UInt, clock
    reg x3 : UInt, clock

    connect x1, cat(mul(x2, in), x2)
    connect x3, shr(x1,2)
    connect x2, tail(x3,2)
    connect out, x1
