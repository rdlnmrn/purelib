module

import TestPurelib.Computation.Machine.Simulation
import TestPurelib.Computation.Machine.Halting
import TestPurelib.Computation.Machine.Invocation
import TestPurelib.Computation.Machine.Halting.Diagonal
import TestPurelib.Approximation.Gaussian.Sequence.HaltingShadow
import TestPurelib.Approximation.Gaussian.Sequence.HaltingShadow.Observation
import TestPurelib.Approximation.Gaussian.Sequence.HaltingShadow.Classifier

/-! # Native finite coded-machine regression entry point -/

/-- Execute finite coded-machine boundaries without an oracle or external program provider. -/
public def main : IO Unit := do
  TestPurelib.Computation.Machine.Simulation.run
  TestPurelib.Computation.Machine.Halting.run
  TestPurelib.Computation.Machine.Invocation.run
  TestPurelib.Computation.Machine.Halting.Diagonal.run
  TestPurelib.Approximation.Gaussian.Sequence.HaltingShadow.run
  TestPurelib.Approximation.Gaussian.Sequence.HaltingShadow.Observation.run
  TestPurelib.Approximation.Gaussian.Sequence.HaltingShadow.Classifier.run
