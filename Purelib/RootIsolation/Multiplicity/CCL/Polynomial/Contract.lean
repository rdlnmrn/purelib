module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Basic
import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Index
public import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Persistent
import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Name
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Contract
namespace NonzeroResult

/-- Complete finite contract for one root-stream request. -/
@[expose] def RequestContract
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) (current :
      (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.RootState result) index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat) : Prop :=
  let next := (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootRequest result) index current epsilon positive
    count
  ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootWord result) index current).IsPrefix
    ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootWord result) index next) ∧
    ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootWord result) index next).length =
      ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootWord result) index current).length + count ∧
    (match (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootBox? result) index next,
      (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootBox? result) index current with
      | none, none => True
      | some inner, some outer => inner.Refines outer
      | none, some _ => False
      | some _, none => False) ∧
    (match (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootBox? result) index next with
      | none => True
      | some box => box.diagonalSq ≤ epsilon ^ 2) ∧
    Data.CCL.Transducer.Machine.Semantics.Basic.ExactCursor
      ((Multiplicity.CCL.Polynomial.Name.NonzeroResult.rootName result) index).process
      ((Multiplicity.CCL.Polynomial.Name.NonzeroResult.rootName result) index).state
      ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootMachine result) index next) ∧
    ∀ {left right : Gaussian.Basic.Canonical},
      Data.CCL.Transducer.Mode.Semantics.SemanticMode.possible
          ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootMachine result) index next).mode left →
        Data.CCL.Transducer.Mode.Semantics.SemanticMode.possible
          ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootMachine result) index next).mode right →
        Geometry.Projective.Chordal.Basic.chordalSq
            (Data.CCL.Progressive.Cursor.Image.Machine.image
              ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootMachine result) index next) left)
            (Data.CCL.Progressive.Cursor.Image.Machine.image
              ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootMachine result) index next) right) ≤ epsilon ^
                2

/-- Every computed root request satisfies prefix persistence, exact bit count,
nested-box accuracy, exact raw-parser semantics, and the requested projective
sidecar error. -/
theorem rootRequest_contract
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) (current :
      (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.RootState result) index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat) :
    RequestContract result index current epsilon positive count := by
  refine ⟨(Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootRequest_word_extends result) index current epsilon
    positive count,
    (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootRequest_word_length result) index current epsilon positive
      count,
    (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootRequest_box_refines result) index current epsilon positive
      count,
    (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootRequest_box_accurate result) index current epsilon
      positive count,
    (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootState_exact result) index
      ((Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootRequest result) index current epsilon positive count),
        ?_⟩
  intro left right leftPossible rightPossible
  exact (Multiplicity.CCL.Polynomial.Persistent.NonzeroResult.rootRequest_cylinder_accurate result) index current
    epsilon positive
    count leftPossible rightPossible

end NonzeroResult

end Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Contract

end
