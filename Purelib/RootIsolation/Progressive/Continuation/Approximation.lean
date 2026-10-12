module

public import Purelib.Approximation.Gaussian.Enclosure.Ball.Box
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Rat.Bounds.AccuracyRadius
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
public import Purelib.RootIsolation.Progressive.Continuation.Basic
import Purelib.Tactic.Ring
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample

open Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table (CoefficientTable)

open Purelib.Approximation.Gaussian

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Continuation.Basic
open Purelib.Data.Gaussian
namespace RootContinuation

/-- One root owner as a progressive squared-error process.  Its possible
values are exactly the rational points in the current certified box, and a
process refinement invokes the common coefficient/root continuation step. -/
def toProcess
    {initialTable : CoefficientTable}
    (continuation : Progressive.Continuation.Basic.RootContinuation initialTable)
    (index : continuation.Index) : Approximation.Gaussian.Process where
  State := continuation.State
  ball state :=
    Enclosure.Ball.ofBox (continuation.box state index)
  Possible state value := (continuation.box state index).Contains value
  witness state :=
    ⟨(continuation.box state index).anchor,
      (continuation.box state index).contains_anchor⟩
  possible_inside := by
    intro state value possible
    exact Enclosure.Ball.contains_ofBox possible
  refine state target positive :=
    continuation.refine state
      (Data.Rat.Bounds.AccuracyRadius.accuracyRadius target)
      (Data.Rat.Bounds.AccuracyRadius.accuracyRadius_pos positive)
  refine_persists := by
    intro state target positive value possible
    exact (continuation.nested state
      (Data.Rat.Bounds.AccuracyRadius.accuracyRadius target)
      (Data.Rat.Bounds.AccuracyRadius.accuracyRadius_pos positive) index).contains
        possible
  accurate := by
    intro state target positive
    exact (continuation.accurate state
      (Data.Rat.Bounds.AccuracyRadius.accuracyRadius target)
      (Data.Rat.Bounds.AccuracyRadius.accuracyRadius_pos positive) index).trans_lt
        (Data.Rat.Bounds.AccuracyRadius.accuracyRadius_sq_lt positive)
  centerBound :=
    (continuation.box continuation.initial index).normSqBound
  centerBound_nonneg :=
    (continuation.box continuation.initial index).normSqBound_nonneg
  center_bounded := by
    intro state
    exact (continuation.box continuation.initial index).normSq_le_normSqBound
      ((continuation.refinesInitial state index).contains
        (continuation.box state index).contains_anchor)
end RootContinuation

end Purelib.RootIsolation.Progressive.Continuation.Basic

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Continuation.Basic
open Purelib.Data.Gaussian
namespace RootContinuation

/-- The arithmetic-ready CCL name belonging to one persistent root owner. -/
def rootNameAt
    {initialTable : CoefficientTable}
    (continuation : Progressive.Continuation.Basic.RootContinuation initialTable)
    (index : continuation.Index) : Name.Basic.Named :=
  { process := continuation.toProcess index
    state := continuation.initial }
end RootContinuation

end Purelib.RootIsolation.Progressive.Continuation.Basic

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Continuation.Basic
open Purelib.Data.Gaussian
namespace RootContinuation

/-- The complete degree-indexed family of arithmetic-ready root names. -/
def rootNames
    {initialTable : CoefficientTable}
    (continuation : Progressive.Continuation.Basic.RootContinuation initialTable) :
    Fin initialTable.degree → Name.Basic.Named :=
  continuation.rootNameAt
end RootContinuation

end Purelib.RootIsolation.Progressive.Continuation.Basic

end
