module

import TestPurelib.Integration.Circle

/-- Execute the retained circle program's actual coarse sample and paid closed-primitive comparison. -/
public def main : IO Unit :=
  TestPurelib.Integration.Circle.checkClosedPrimitive
