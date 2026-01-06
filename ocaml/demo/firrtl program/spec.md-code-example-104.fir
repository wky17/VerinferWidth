FIRRTL version 4.0.0
circuit Foo:
  module Foo:
    node a =
      ;; snippetbegin
      UInt(42)
      ;; snippetend
    node b =
      ;; snippetbegin
      UInt("b101010")
      ;; snippetend
    node c =
      ;; snippetbegin
      UInt("o52")
      ;; snippetend
    node d =
      ;; snippetbegin
      UInt("h2A")
      ;; snippetend
    node e =
      ;; snippetbegin
      UInt("h2a")
      ;; snippetend
