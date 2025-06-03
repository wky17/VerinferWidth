circuit DownCounter :
  module DownCounter :
    input clock : Clock
    input reset1 : UInt<1>
    output io : { cnt : UInt<8>, tick : UInt<1>}

    reg cntReg : UInt, clock with :
      reset => (reset1, UInt<4>("h9")) @[Counter.scala 60:23]
