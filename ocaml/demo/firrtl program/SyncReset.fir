circuit SyncReset :
  module WhenCounter :
    input clock1 : Clock
    input reset1 : Reset
    output io : { cnt : UInt<8>, tick : UInt<1>}

    reg cntReg : UInt<8>, clock1 with :
      reset => (reset1, UInt<8>("h0")) @[Counter.scala 29:23]
    node _cntReg_T = add(cntReg, UInt<1>("h1")) @[Counter.scala 31:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Counter.scala 31:20]
    cntReg <= _cntReg_T_1 @[Counter.scala 31:10]
    node _T = eq(cntReg, UInt<3>("h4")) @[Counter.scala 32:15]
    when _T : @[Counter.scala 32:22]
    {
      cntReg <= UInt<1>("h0") @[Counter.scala 33:12]
    }
    node _io_tick_T = eq(cntReg, UInt<3>("h4")) @[Counter.scala 37:21]
    io.tick <= _io_tick_T @[Counter.scala 37:11]
    io.cnt <= cntReg @[Counter.scala 38:10]

  module SyncReset :
    input clock : Clock
    input reset1 : UInt<1>
    output io : { value : UInt}

    reg syncReset_REG : UInt<1>, clock with :
      reset => (UInt<1>("h0"), syncReset_REG) @[SyncReset.scala 9:34]
    syncReset_REG <= reset1 @[SyncReset.scala 9:34]
    reg syncReset : UInt<1>, clock with :
      reset => (UInt<1>("h0"), syncReset) @[SyncReset.scala 9:26]
    syncReset <= syncReset_REG @[SyncReset.scala 9:26]
    inst cnt aof WhenCounter @[SyncReset.scala 10:19]
    cnt.clock1 <= clock
    cnt.reset1 <= reset1
    cnt.reset1 <= syncReset @[SyncReset.scala 11:13]
    io.value <= cnt.io.cnt @[SyncReset.scala 13:12]
