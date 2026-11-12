module

import Purelib.Polynomial.Approximation.Gaussian.Residual.Conjugation
import Purelib.Polynomial.Approximation.Gaussian.Residual.Reciprocal
import Purelib.Approximation.Gaussian.Division.Prepared.Rational
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Bounds.Quarter
meta import Purelib.Polynomial.Approximation.Gaussian.Residual.Conjugation
meta import Purelib.Polynomial.Approximation.Gaussian.Residual.Reciprocal
meta import Purelib.Approximation.Gaussian.Division.Prepared.Rational
meta import Purelib.Approximation.Gaussian.Name.Sampling
meta import Purelib.Data.Gaussian.Field

/-! # Unary arbitrary-degree residual operations on the same original channels -/

namespace TestPurelib.Polynomial.UnaryResiduals

open Purelib
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Approximation.Gaussian (Residual)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Data.Gaussian.Basic (Canonical)

example {polynomial : CoefficientPolynomial} {channel : CoherentNamed} (residual : Residual polynomial channel) :
    Residual (Polynomial.Dense.Gaussian.Conjugation.conjugate polynomial) (CoherentNamed.conj channel) := residual.conj

example {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} {prepared : Prepared channel}
    (cache : Residual.Reciprocal residual prepared) :
    Residual cache.annihilator (prepared.quotient (CoherentNamed.Coherence.exact 1)) := cache.residualCertificate

example {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} {prepared : Prepared channel}
    (cache : Residual.Reciprocal residual prepared) (index : Nat) :
    cache.residualCertificate.source.sample index =
      (residual.source.sample (cache.comparison.leftIndex + index))⁻¹ := by
  rw [cache.residualCertificate_source]
  exact cache.sample index

/-- An exact cubic residual retains a nonreal point and its original complex coefficient polynomial. -/
private def complexCubic : Residual (⟨[1, 0, 0, ⟨2, -2⟩]⟩ : CoefficientPolynomial)
    (CoherentNamed.Coherence.exact (⟨1, 1⟩ : Canonical)) := by
  let exact := Residual.exact (⟨1, 1⟩ : Canonical)
  refine ⟨by decide, exact.source, exact.equivalent, 0, by decide, ?_⟩
  intro index
  rw [Residual.exact_sample]
  have zero : (⟨[1, 0, 0, ⟨2, -2⟩]⟩ : CoefficientPolynomial).eval (⟨1, 1⟩ : Canonical) = 0 := by decide
  rw [zero, Data.Gaussian.Norm.Basic.normSq_zero]
  exact Approximation.Rational.Geometric.Basic.quarterRadius_nonneg (by decide) index

/-- A cubic with an original zero factor retains the nonzero root two and a zero residual scale. -/
private def zeroFactorCubic : Residual (⟨[1, -2, 0, 0]⟩ : CoefficientPolynomial)
    (CoherentNamed.Coherence.exact 2) := by
  let exact := Residual.exact 2
  refine ⟨by decide, exact.source, exact.equivalent, 0, by decide, ?_⟩
  intro index
  rw [Residual.exact_sample]
  have zero : (⟨[1, -2, 0, 0]⟩ : CoefficientPolynomial).eval 2 = 0 := by decide
  rw [zero, Data.Gaussian.Norm.Basic.normSq_zero]
  exact Approximation.Rational.Geometric.Basic.quarterRadius_nonneg (by decide) index

/-- Execute complex conjugation and a checked reciprocal whose original polynomial loses degree after reversal. -/
private def checkUnaryResiduals : IO Unit := do
  let conjugate := complexCubic.conj
  unless conjugate.source.sample 5 = (⟨1, -1⟩ : Canonical) ∧ conjugate.scale = 0 do
    throw (IO.userError "conjugation lost the original complex cubic sample or residual scale")
  let source := zeroFactorCubic
  let prepared := (RationalSidecar.exact 2).prepare (by decide)
  let cache := Residual.Reciprocal.ofPrepared source prepared
  let certificate := cache.residualCertificate
  unless certificate.source.sample 7 = (2 : Canonical)⁻¹ ∧ certificate.scale = 0 ∧
      (Residual.Reciprocal.polynomial (⟨[1, -2, 0, 0]⟩ : CoefficientPolynomial)).natDegree = 2 do
    throw (IO.userError "reciprocal lost the actual original tail, zero scale or reversed degree drop")
  let target := ((1 : Data.Rat.Fraction.Rational) / 4) / 4 / 4
  let comparison := cache.equivalent.compare 2 3 target
    (Data.Rat.Bounds.Quarter.quarter_pos
      (Data.Rat.Bounds.Quarter.quarter_pos (Data.Rat.Bounds.Quarter.quarter_pos (by decide))))
  let actual := (Name.Sampling.approximation (prepared.quotient (CoherentNamed.Coherence.exact 1)).name).sample
    comparison.leftIndex
  let retained := (Name.Sampling.approximation cache.result.toApproximation.toNamed).sample comparison.rightIndex
  unless Data.Gaussian.Norm.Basic.normSq (actual - retained) < target do
    throw (IO.userError "actual prepared quotient disagreed with its retained reciprocal cache")

#eval checkUnaryResiduals

end TestPurelib.Polynomial.UnaryResiduals
