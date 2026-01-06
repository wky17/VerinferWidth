circuit Foo:
  module Foo :
    input clock : Clock
    output io : UInt<10>

    reg a1 : UInt, clock
    a1 <= shr(sub(a1,UInt<1>(0)),1)
    a1 <= UInt<1>(0)
    io <= a1