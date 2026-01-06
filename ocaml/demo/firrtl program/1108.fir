circuit top_mod :
  module top_mod :
    input sel: UInt<1>
    output tmp116: UInt
    tmp116 <= mux(sel, UInt<8>(24), UInt<8>(42))