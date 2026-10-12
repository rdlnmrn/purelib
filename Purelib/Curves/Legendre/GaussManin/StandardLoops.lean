module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Vector.Operational.Basic
public import Purelib.Approximation.Matrix.Operational.Integral.Action
public import Purelib.Curves.Legendre.Monodromy
import Purelib.Curves.Legendre.Paths
public import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.LinearAlgebra.Matrix.Multiplication

open Purelib

open Purelib.Approximation.Gaussian.Vector

open Purelib.Approximation.Gaussian.Vector.Operational.Basic

open Purelib.Approximation.Matrix.Operational.Integral

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Periods

open Purelib.Topology.Knot.Braid.ThreeStrand.Integral

section
public section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

namespace Purelib.Curves.Legendre.GaussManin.StandardLoops

set_option genInjectivity false in
/-- Unconditional productive period columns for the three standard closed loops. These use actual base-fibre period
programs and the dual action of the certified homology matrices; no impossible equality between different fibres is
requested. -/
structure StandardLoopContinuations {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (loops : Monodromy.StandardLoops frame) where
  /-- The original certified base-fibre period programs shared by all retained standard loop actions. -/ base :
    Fibre.FibreData frame

constructive_injectivity Purelib.Curves.Legendre.GaussManin.StandardLoops.StandardLoopContinuations

namespace StandardLoopContinuations

/-- Apply the certified zero-loop dual matrix to the retained base period column. -/
@[expose] def zero {parameter :
  Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (continuations : Curves.Legendre.GaussManin.StandardLoops.StandardLoopContinuations loops) :
      Operational.Basic.RawPeriodVector :=
  Action.matrixAction
    (Dual.periodMatrix loops.zeroPath.word)
    continuations.base.rawPeriods

/-- Apply the certified one-loop dual matrix to the retained base period column. -/
@[expose] def one {parameter :
  Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (continuations : Curves.Legendre.GaussManin.StandardLoops.StandardLoopContinuations loops) :
      Operational.Basic.RawPeriodVector :=
  Action.matrixAction
    (Dual.periodMatrix loops.onePath.word)
    continuations.base.rawPeriods

/-- Apply the derived infinity-loop dual matrix to the retained base period column. -/
@[expose] def infinity {parameter :
  Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (continuations : Curves.Legendre.GaussManin.StandardLoops.StandardLoopContinuations loops) :
      Operational.Basic.RawPeriodVector :=
  Action.matrixAction
    (Dual.periodMatrix
      loops.infinityPath.word)
    continuations.base.rawPeriods

/-- Apply the concatenated standard-loop product dual matrix to the retained base period column. -/
@[expose] def product {parameter :
  Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (continuations : Curves.Legendre.GaussManin.StandardLoops.StandardLoopContinuations loops) :
      Operational.Basic.RawPeriodVector :=
  Action.matrixAction
    (Dual.periodMatrix loops.productPath.word)
    continuations.base.rawPeriods

/-- The certified zero-loop period output agrees operationally with the displayed standard zero matrix action. -/
@[expose] def zero_explicit {parameter
  : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (continuations : Curves.Legendre.GaussManin.StandardLoops.StandardLoopContinuations loops) :
    Operational.Basic.VectorEquivalent continuations.zero
      (Action.matrixAction Monodromy.zeroPeriodMatrix
        continuations.base.rawPeriods) := by
  rw [zero, loops.zeroPath_periodMatrix]
  exact VectorEquivalent.refl _

/-- The certified one-loop period output agrees operationally with the displayed standard one matrix action. -/
@[expose] def one_explicit {parameter
  : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (continuations : Curves.Legendre.GaussManin.StandardLoops.StandardLoopContinuations loops) :
    Operational.Basic.VectorEquivalent continuations.one
      (Action.matrixAction Monodromy.onePeriodMatrix
        continuations.base.rawPeriods) := by
  rw [one, loops.onePath_periodMatrix]
  exact VectorEquivalent.refl _

/-- The derived infinity-loop period output agrees operationally with the displayed standard infinity matrix action. -/
@[expose] def infinity_explicit
  {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (continuations : Curves.Legendre.GaussManin.StandardLoops.StandardLoopContinuations loops) :
    Operational.Basic.VectorEquivalent continuations.infinity
      (Action.matrixAction Monodromy.infinityPeriodMatrix
        continuations.base.rawPeriods) := by
  rw [infinity, loops.infinityPath_periodMatrix]
  exact VectorEquivalent.refl _

/-- The certified standard-loop product returns the original base period column operationally. -/
@[expose] def product_identity
  {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    {loops : Monodromy.StandardLoops frame}
    (continuations : Curves.Legendre.GaussManin.StandardLoops.StandardLoopContinuations loops) :
    Operational.Basic.VectorEquivalent continuations.product continuations.base.rawPeriods := by
  rw [product, loops.productPath_periodMatrix]
  exact Action.matrixAction_identity continuations.base.rawPeriods

end StandardLoopContinuations
end Purelib.Curves.Legendre.GaussManin.StandardLoops

end
