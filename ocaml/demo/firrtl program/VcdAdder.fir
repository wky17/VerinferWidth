circuit VcdAdder :
  module DoAdd :
    input clock1 : Clock
    input a : SInt<8>
    input b : SInt<8>
    output c : SInt<10>

    reg accum : SInt, clock1

    accum <= add(a, b)
    c <= accum

  module VcdAdder :
    input clock : Clock
    input io_a : SInt<8>
    input io_b : SInt<8>
    output io_c : SInt<10>

    inst do_add aof DoAdd

    do_add.clock1 <= clock
    do_add.a <= io_a
    do_add.b <= io_b

    io_c <= do_add.c
