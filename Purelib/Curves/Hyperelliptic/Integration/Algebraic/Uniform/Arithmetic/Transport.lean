module

public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Transport

/-! # Exact common-request transport of retained arithmetic/uniform comparisons

The original numeric Reading and complete comparison are reindexed together
along equality of their whole accuracy requests. Both selected comparison
samples and states, cached interpretation and original uniform query remain
unchanged. This operation executes no interpretation or comparison factory.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation.ArithmeticComparison

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation (Reading RootObservation)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : OddPowerDifferential curve.polynomial}
    {start finish : LiftedPoint 2} {lifted : LiftedCell start finish} {cell : CellModel} {time : Rational}
    {uniform : UniformObservation curve differential lifted cell time}
    {point : Canonical} {sheet : CoherentNamed} {apart : Named.Apart sheet.name}
    {state : sheet.name.process.State} {rootObservation : RootObservation} {first last : AccuracyRequest}
    {numeric : Reading differential point sheet apart state rootObservation first}
    {identity : PowerIdentity sheet 2 (curve.polynomial.eval point)}

/-- Transport the SAME numeric Reading and whole original query comparison to an exactly equal common request. -/
@[expose] def castAccuracy (equal : first = last) (retained : ArithmeticComparison uniform numeric identity) :
    ArithmeticComparison uniform (numeric.castAccuracy equal) identity := by
  cases equal
  exact retained

/-- The common-request view retains the entire original comparison/interpretation pair heterogeneously. -/
theorem castAccuracy_heq (equal : first = last) (retained : ArithmeticComparison uniform numeric identity) :
    HEq (retained.castAccuracy equal) retained := by
  cases equal
  rfl

/-- The already selected left sample keeps its original index after exact common-request transport. -/
theorem castAccuracy_leftIndex (equal : first = last) (retained : ArithmeticComparison uniform numeric identity) :
    (retained.castAccuracy equal).comparison.tail.leftIndex = retained.comparison.tail.leftIndex := by
  cases equal
  rfl

/-- The actual selected right sample keeps its independent original index without a comparison replay. -/
theorem castAccuracy_rightIndex (equal : first = last) (retained : ArithmeticComparison uniform numeric identity) :
    (retained.castAccuracy equal).comparison.tail.rightIndex = retained.comparison.tail.rightIndex := by
  cases equal
  rfl

/-- Reindex the retained comparison along equality of its original uniform query time.

The original numeric Reading, whole interpreted comparison and selected
sample pair are transported unchanged. The query is the equality-cast
original observation; no observation or comparison factory executes.
-/
@[expose] def castTime {other : Rational} (equal : other = time)
    (retained : ArithmeticComparison uniform numeric identity) :
    ArithmeticComparison
      (Eq.mpr (congrArg (UniformObservation curve differential lifted cell) equal) uniform)
      numeric identity := by
  cases equal
  exact retained

/-- Query-time transport retains the complete original interpretation/comparison pair. -/
theorem castTime_heq {other : Rational} (equal : other = time)
    (retained : ArithmeticComparison uniform numeric identity) :
    HEq (retained.castTime equal) retained := by
  cases equal
  rfl

/-- Query-time transport preserves both original selected comparison sample indices. -/
theorem castTime_indices {other : Rational} (equal : other = time)
    (retained : ArithmeticComparison uniform numeric identity) :
    (retained.castTime equal).comparison.tail.leftIndex = retained.comparison.tail.leftIndex ∧
      (retained.castTime equal).comparison.tail.rightIndex = retained.comparison.tail.rightIndex := by
  cases equal
  exact ⟨rfl, rfl⟩

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation.ArithmeticComparison

end
