FIRRTL version 4.0.0
circuit Foo:
  module Foo:
    node a =
      ;; snippetbegin
      SInt(-42)
      ;; snippetend
    node b =
      ;; snippetbegin
      SInt("b-101010")
      ;; snippetend
    node c =
      ;; snippetbegin
      SInt("o-52")
      ;; snippetend
    node d =
      ;; snippetbegin
      SInt("h-2A")
      ;; snippetend
    node e =
      ;; snippetbegin
      SInt("h-2a")
      ;; snippetend
