FIRRTL version 2.0.0
circuit Datapath : 
  module Datapath : 
    input clock : Clock
    reg x1 : UInt, clock
    reg y1 : UInt, clock
    reg y2 : UInt, clock
    reg z1 : UInt, clock
    reg z2 : UInt, clock
    
    x1 <= add(y1, shr(y2,2))
    y1 <= rem(shr(z1,2), shl(z2,2))
    z1 <= x1
    z2 <= UInt<1>(0)
    y2 <= UInt<3>(0)
