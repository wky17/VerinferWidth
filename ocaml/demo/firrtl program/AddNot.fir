circuit Foo:
  module Foo:
    input b: UInt<1>
    output a: UInt

    when b:
    {
      a <= UInt(1)
    }
    else:
    {
      a <= UInt(1)
 }

