circuit TrueDualPortMemory :
  module TrueDualPortMemory :
    input clock : Clock
    input reset1 : UInt<1>
    output io : { flip addrA : UInt<10>, rdDataA : UInt<8>, flip wrEnaA : UInt<1>, flip wrDataA : UInt<8>, flip addrB : UInt<10>, rdDataB : UInt<8>, flip wrEnaB : UInt<1>, flip wrDataB : UInt<8>}

    smem mem : UInt<8> [1024] @[memory.scala 68:24]
    wire _io_rdDataA_WIRE : UInt @[memory.scala 70:25]
    _io_rdDataA_WIRE is invalid @[memory.scala 70:25]
    when UInt<1>("h1") : @[memory.scala 70:25]
    {
      _io_rdDataA_WIRE <= io.addrA @[memory.scala 70:25]
      node _io_rdDataA_T = or(_io_rdDataA_WIRE, UInt<10>("h0")) @[memory.scala 70:25]
      node _io_rdDataA_T_1 = bits(_io_rdDataA_T, 9, 0) @[memory.scala 70:25]
      read mport io_rdDataA_MPORT = mem[_io_rdDataA_T_1], clock @[memory.scala 70:25]
    }
    io.rdDataA <= io_rdDataA_MPORT @[memory.scala 70:14]
    when io.wrEnaA : @[memory.scala 71:19]
    {
      write mport MPORT = mem[io.addrA], clock
      MPORT <= io.wrDataA
    }
    wire _io_rdDataB_WIRE : UInt @[memory.scala 74:25]
    _io_rdDataB_WIRE is invalid @[memory.scala 74:25]
    when UInt<1>("h1") : @[memory.scala 74:25]
    {
      _io_rdDataB_WIRE <= io.addrB @[memory.scala 74:25]
      node _io_rdDataB_T = or(_io_rdDataB_WIRE, UInt<10>("h0")) @[memory.scala 74:25]
      node _io_rdDataB_T_1 = bits(_io_rdDataB_T, 9, 0) @[memory.scala 74:25]
      read mport io_rdDataB_MPORT = mem[_io_rdDataB_T_1], clock @[memory.scala 74:25]
    }
    io.rdDataB <= io_rdDataB_MPORT @[memory.scala 74:14]
    when io.wrEnaB : @[memory.scala 75:19]
    {
      write mport MPORT_1 = mem[io.addrB], clock
      MPORT_1 <= io.wrDataB
 }


