circuit top_mod :
  module top_mod :
    output tmp891: SInt<1>
    wire tmp871: UInt
    tmp871 <= ahead(SInt<18>(42), 0)
    tmp891 <= cvt(tmp871)