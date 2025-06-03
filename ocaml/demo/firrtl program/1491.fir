circuit top_mod :
  module top_mod :
    input sel: UInt<1>
    input t: UInt<1>
    input f: UInt<1>
    output out: UInt

    out <= mux(sel, t, f)
