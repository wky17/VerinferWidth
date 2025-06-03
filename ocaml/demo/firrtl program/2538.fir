circuit Example :
  module Example :
    input clock: Clock 
    input reset1: UInt<1>
    input in: UInt<2>
    output out: UInt<2>
    node _out_T = add(in, in)
    node _out_T_1 = tail(_out_T, 1)
    out <= _out_T_1
