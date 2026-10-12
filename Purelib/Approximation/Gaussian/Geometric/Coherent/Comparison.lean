module
import Purelib.Approximation.Gaussian.Arithmetic.Sampling
public import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Data.Gaussian.Basic
import Mathlib.Algebra.Group.Defs
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Coherent

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Geometric

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Gaussian.Sequence.Name

open Purelib.Riemann.Periods

section
@[expose] public section

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

namespace Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison

/-- A synchronized constant geometric stream is operationally the ordinary terminating coherent constant. -/
def geometricExact_equivalent_exact
    (value : Data.Gaussian.Basic.Canonical) :
    Gaussian.Equivalence.NamedEquivalent
      (PeriodMatrix.geometricNamed
        (GeometricApproximation.exact
          value)).name
      (Coherence.exact value).name := by
  let geometric :=
    GeometricApproximation.exact
      value
  let constant := Constant.constantApproximation
    value
  have toConstant : Gaussian.Equivalence.NamedEquivalent (PeriodMatrix.geometricNamed geometric).name
      constant.toNamed := by
    simpa only [PeriodMatrix.geometricNamed,
      Coherent.CoherentNamed.ofApproximation] using
      Equivalence.approximationEquivalent_toNamed
        (Equivalence.approximationEquivalentOfSamplesEq
          geometric.toApproximation constant (by intro index; rfl))
  exact NamedEquivalent.trans toConstant
    (NamedEquivalent.symm
      (Exact.exact_toConstantNamed value))

/-- The synchronized geometric zero used by `sumNamed` is operationally the ordinary terminating coherent zero. -/
def geometricZero_equivalent_exact :
    Gaussian.Equivalence.NamedEquivalent
      (PeriodMatrix.geometricNamed
        (GeometricApproximation.exact
          0)).name
      (Coherence.exact 0).name :=
  geometricExact_equivalent_exact 0

/-- Equal-index geometric negation is the operational additive inverse of the geometric source, hence agrees with the
actual stateful CCL negation. -/
def geometricNeg_equivalent_statefulNeg
    (source : Gaussian.Geometric.GeometricApproximation) :
    Gaussian.Equivalence.NamedEquivalent
      (PeriodMatrix.geometricNamed
        (GeometricApproximation.neg
          source)).name
      (CoherentNamed.neg
        (PeriodMatrix.geometricNamed source)).name := by
  let value := PeriodMatrix.geometricNamed source
  let candidate := PeriodMatrix.geometricNamed
    (GeometricApproximation.neg source)
  let geometricZero := PeriodMatrix.geometricNamed
    (GeometricApproximation.exact 0)
  have cancelToGeometricZero : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add value candidate).name
      geometricZero.name := by
    simpa only [value, candidate, geometricZero, PeriodMatrix.geometricNamed,
      CoherentNamed.add,
      Coherent.CoherentNamed.ofApproximation] using
      Sampling.addToNamed_equivalent_pointwise
        source.toApproximation
        (GeometricApproximation.neg
          source).toApproximation
        (GeometricApproximation.exact
          0).toApproximation
        (by
          intro index
          simp only [
            Gaussian.Geometric.GeometricApproximation.toApproximation_sample,
            Gaussian.Geometric.GeometricApproximation.exact_sample,
            Gaussian.Geometric.GeometricApproximation.neg_sample]
          exact (add_neg_cancel (source.sample index)).symm)
  have cancel : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add value candidate).name
      (Coherence.exact 0).name :=
    NamedEquivalent.trans cancelToGeometricZero
      geometricZero_equivalent_exact
  simpa only [value, candidate] using
    Additive.equivalent_neg_of_add_zero value candidate cancel

/-- Stateful negation of any realization of a synchronized geometric source realizes the equal-index geometric negation.
-/
def coherentNeg_equivalent_geometricNeg
    (value : Coherent.CoherentNamed)
    (source : Gaussian.Geometric.GeometricApproximation)
    (equivalent : Gaussian.Equivalence.NamedEquivalent value.name
      (PeriodMatrix.geometricNamed source).name) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.neg value).name
      (PeriodMatrix.geometricNamed
        (GeometricApproximation.neg
          source)).name :=
  NamedEquivalent.trans
    (Additive.coherentNeg_respects value (PeriodMatrix.geometricNamed source) equivalent)
    (NamedEquivalent.symm
      (geometricNeg_equivalent_statefulNeg source))

/-- Actual addition realizes equal-index geometric addition whenever both operands realize their synchronized sources.
-/
def coherentAdd_equivalent_geometricAdd
    (left right : Coherent.CoherentNamed)
    (leftSource rightSource :
      Gaussian.Geometric.GeometricApproximation)
    (leftEquivalent : Gaussian.Equivalence.NamedEquivalent left.name
      (PeriodMatrix.geometricNamed leftSource).name)
    (rightEquivalent : Gaussian.Equivalence.NamedEquivalent right.name
      (PeriodMatrix.geometricNamed rightSource).name) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add left right).name
      (PeriodMatrix.geometricNamed
        (GeometricApproximation.add
          leftSource rightSource)).name := by
  let leftGeometric := PeriodMatrix.geometricNamed leftSource
  let rightGeometric := PeriodMatrix.geometricNamed rightSource
  have replaceOperands : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add left right).name
      (CoherentNamed.add
        leftGeometric rightGeometric).name :=
    Congruence.coherentAdd_respects
      left leftGeometric right rightGeometric
      leftEquivalent rightEquivalent
  apply NamedEquivalent.trans replaceOperands
  simpa only [leftGeometric, rightGeometric, PeriodMatrix.geometricNamed,
    CoherentNamed.add,
    Coherent.CoherentNamed.ofApproximation] using
    Sampling.addToNamed_equivalent_pointwise
      leftSource.toApproximation rightSource.toApproximation
      (GeometricApproximation.add
        leftSource rightSource).toApproximation
      (by intro index; rfl)

end Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison

end
