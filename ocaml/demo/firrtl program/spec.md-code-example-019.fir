FIRRTL version 4.0.0
circuit Foo:
  ;; snippetbegin
  module Foo :
    wire v : UInt[3]
    connect v[0], UInt(0)
    connect v[1], UInt(10)
    connect v[2], UInt(42)
  ;; snippetend
