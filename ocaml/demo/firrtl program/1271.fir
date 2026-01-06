circuit Bar :
  module Bar :
    input clock : Clock
    input cond : UInt<1>

    reg a : UInt, clock

    node _false = add(a, UInt<1>(0))
    node false = tail(_false, 1)
    a <= mux(cond, UInt<2>(0), false)
