firrtl.circuit "ParamFunc" {
  firrtl.module @ParamFunc(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io: !firrtl.bundle<selA flip: uint<1>, resA: uint<5>, selB flip: uint<1>, resB: bundle<d: uint<10>, b: uint<1>>>) attributes {convention = #firrtl<convention scalarized>} {
    %resA = firrtl.wire : !firrtl.uint<4>
    %tVal = firrtl.wire : !firrtl.bundle<d: uint<10>, b: uint<1>>
    %fVal = firrtl.wire : !firrtl.bundle<d: uint<10>, b: uint<1>>
    %resB = firrtl.wire : !firrtl.bundle<d: uint<10>, b: uint<1>>
