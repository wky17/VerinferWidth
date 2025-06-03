FIRRTL version 4.0.0
circuit Bar:
  ;; snippetbegin
  module Bar :
    output io : { x : UInt, flip y : UInt<8> }
    connect io.x, add(io.y, UInt(1))
  ;; snippetend
