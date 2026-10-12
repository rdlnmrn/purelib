module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Vector.Operational.Basic
public import Purelib.Approximation.Matrix.Operational.Integral.Action
import Purelib.Curves.Legendre.Paths
public import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.LinearAlgebra.Matrix.Integral.Transpose
public import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Words
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Topology.Knot.Braid.Word.Basic

open Purelib

open Purelib.Approximation.Gaussian.Vector

open Purelib.Approximation.Gaussian.Vector.Operational.Basic

open Purelib.Approximation.Matrix.Operational.Integral

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Paths

open Purelib.Curves.Legendre.Periods

open Purelib.LinearAlgebra.Matrix.Integral

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

namespace Purelib.Curves.Legendre.GaussManin.Endpoint

/-! ## Finite endpoint continuation and the dual period action -/

set_option genInjectivity false in
/-- Actual endpoint period programs together with the source fibre whose displayed homology basis is transported along a
finite parameter path. No claim equates periods on the two different endpoint curves. -/
structure EndpointContinuation {start finish :
  Data.Gaussian.Basic.Canonical}
    {left : Paths.Frame start} {right : Paths.Frame finish}
    (path : Paths.Path left right) where
  /-- The certified raw period programs on the original source frame curve. -/ source : Fibre.FibreData left
  /-- The certified raw period programs on the actual target frame curve. -/ target : Fibre.FibreData right

constructive_injectivity Purelib.Curves.Legendre.GaussManin.Endpoint.EndpointContinuation

namespace EndpointContinuation

/-- Endpoint periods evaluated on the transported source-labelled homology basis. Since `wordMatrix` acts on homology
coordinate columns, the period column carries its exact transpose. -/
@[expose] def periods {start finish :
  Data.Gaussian.Basic.Canonical}
    {left : Paths.Frame start} {right : Paths.Frame finish}
    {path : Paths.Path left right} (continuation : Curves.Legendre.GaussManin.Endpoint.EndpointContinuation path) :
    Operational.Basic.RawPeriodVector :=
  Action.matrixAction
    (Dual.periodMatrix path.word)
    continuation.target.rawPeriods

/-- The coefficient used for an output basis period is exactly the corresponding column coefficient of direct homology
transport. -/
@[simp] theorem period_coefficient {start finish
  : Data.Gaussian.Basic.Canonical}
    {left : Paths.Frame start} {right : Paths.Frame finish}
    {path : Paths.Path left right} (_continuation : Curves.Legendre.GaussManin.Endpoint.EndpointContinuation path)
    (output input : Fin 2) :
    Dual.periodMatrix path.word output input =
      Words.wordMatrix path.word input output :=
  Transpose.transpose_apply _ _ _

/-- The empty path leaves the actual endpoint period column unchanged. -/
@[expose] def nil_periods {parameter :
  Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (data : Fibre.FibreData frame) :
    Operational.Basic.VectorEquivalent
      (({ source := data, target := data } :
        Curves.Legendre.GaussManin.Endpoint.EndpointContinuation (.nil frame)).periods)
      data.rawPeriods := by
  change Operational.Basic.VectorEquivalent
    (Action.matrixAction
      (Dual.periodMatrix []) data.rawPeriods)
    data.rawPeriods
  rw [Dual.periodMatrix_nil]
  exact Action.matrixAction_identity data.rawPeriods

/-- The exact dual matrix for an appended path acts in the order forced by pairing endpoint periods with the composed
homology transport. -/
@[expose] def append_periods {start middle
  finish : Data.Gaussian.Basic.Canonical}
    {left : Paths.Frame start} {center : Paths.Frame middle} {right : Paths.Frame finish}
    (first : Paths.Path left center) (second : Paths.Path center right)
    (source : Fibre.FibreData left) (target : Fibre.FibreData right) :
    let appended : Curves.Legendre.GaussManin.Endpoint.EndpointContinuation (first.append second) :=
      { source := source, target := target }
    Operational.Basic.VectorEquivalent appended.periods
      (Action.matrixAction
        (Dual.periodMatrix first.word)
        (Action.matrixAction
          (Dual.periodMatrix second.word)
          target.rawPeriods)) := by
  intro appended
  change Operational.Basic.VectorEquivalent
    (Action.matrixAction
      (Dual.periodMatrix
        (first.append second).word) target.rawPeriods)
    (Action.matrixAction
      (Dual.periodMatrix first.word)
      (Action.matrixAction
        (Dual.periodMatrix second.word)
        target.rawPeriods))
  rw [Path.word_append,
    Dual.periodMatrix_append]
  exact Action.matrixAction_mul _ _ target.rawPeriods

/-- Applying the reverse dual action after the forward one returns the canonical endpoint period column operationally.
-/
@[expose] def reverse_undoes_periods {start
  finish : Data.Gaussian.Basic.Canonical}
    {left : Paths.Frame start} {right : Paths.Frame finish}
    (path : Paths.Path left right) (target : Fibre.FibreData right) :
    Operational.Basic.VectorEquivalent
      (Action.matrixAction
        (Dual.periodMatrix path.reverse.word)
        (Action.matrixAction
          (Dual.periodMatrix path.word)
          target.rawPeriods))
      target.rawPeriods := by
  rw [Path.word_reverse]
  have inverse :=
    (Dual.periodMatrix_inverse_identities
      path.word).2
  apply VectorEquivalent.trans
    (VectorEquivalent.symm
      (Action.matrixAction_mul
        (Dual.periodMatrix path.word.inverse)
        (Dual.periodMatrix path.word)
        target.rawPeriods))
  rw [inverse]
  exact Action.matrixAction_identity target.rawPeriods

end EndpointContinuation
end Purelib.Curves.Legendre.GaussManin.Endpoint

end
