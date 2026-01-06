circuit Widths:
  module Widths:
    input x : UInt<1>
    input y : UInt<2>
    output out1 : UInt
    output out2 : UInt

    wire w : UInt
    w <= x
    w <= y

    out1 <= w

    wire wx : UInt
    wx <= x

    out2 <= wx
