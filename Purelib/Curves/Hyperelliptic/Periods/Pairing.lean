module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Coherent.Additive
public import Purelib.Approximation.Gaussian.Coherent.FiniteSum
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Matrix
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Integration.Path.Lifted.Program
public import Purelib.Integration.Path.Primitive
import Purelib.Integration.Program.Comparison
import Purelib.Integration.Program.Gaussian.Arithmetic
import Purelib.Integration.Program.Gaussian.Name
import Purelib.LinearAlgebra.Matrix.Multiplication
public import Purelib.Topology.Polygon.Stokes
import Init.Core
public import Init.Data.Fin.Lemmas
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Integration.Path.Lifted.Model
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.LinearAlgebra.Gaussian.QuadraticForm
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Algebra

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Coherent

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Geometric

open Purelib.Approximation.Gaussian.Geometric.Coherent

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Basis

open Purelib.Integration

open Purelib.Integration.Path

open Purelib.Integration.Path.Lifted.Program

open Purelib.Integration.Program

open Purelib.Integration.Program.Gaussian.Basic

open Purelib.LinearAlgebra.Matrix

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.PeriodMatrix

open Purelib.Topology.Polygon

section
public section

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

namespace Purelib.Curves.Hyperelliptic.Periods.Pairing

/-- Fraction-free normalized-period numerator. -/
@[expose] def numerator {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve) (row column : Fin genus) :
    Coherent.CoherentNamed :=
  matrixMul data.aInverse.adjugate data.toPeriodData.bMatrix row column

/-- Antisymmetric residual of the fraction-free numerator. -/
@[expose] def numeratorResidual {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve) (row column : Fin genus) :
    Coherent.CoherentNamed :=
  add
    (numerator data row column)
    (neg
      (numerator data column row))

/-- The unnormalized first-bilinear-relation residual `(A Bᵀ - B Aᵀ)ᵢⱼ`. This is the quantity obtained directly by
finite Stokes edge cancellation before applying any inverse or adjugate. -/
@[expose] def periodPairingResidual {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    Coherent.CoherentNamed :=
  add
    (matrixMul data.aMatrix (transpose data.bMatrix) row column)
    (neg
      (matrixMul data.bMatrix (transpose data.aMatrix) row column))

/-- Equal-index geometric realization of the unnormalized first-bilinear residual. Its finite samples use one
synchronized sample of every A- and B-period entry, so they can be read literally as cut-polygon increments. -/
@[expose] def synchronizedPeriodPairingResidual {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    Gaussian.Geometric.GeometricApproximation :=
  GeometricApproximation.sub
    (ScaledInverseCertificate.geometricProductEntry
      (geometricMatrixOfNamed data.aMatrix)
      (ScaledInverseCertificate.geometricTranspose (geometricMatrixOfNamed data.bMatrix))
      row column)
    (ScaledInverseCertificate.geometricProductEntry
      (geometricMatrixOfNamed data.bMatrix)
      (ScaledInverseCertificate.geometricTranspose (geometricMatrixOfNamed data.aMatrix))
      row column)

/-- Every synchronized residual sample is exactly the finite symplectic pairing of the displayed rational A- and
B-period matrices. -/
@[simp] theorem synchronizedPeriodPairingResidual_sample {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) (index : Nat) :
    (synchronizedPeriodPairingResidual data row column).sample index =
      Stokes.symplecticPairing
        (sampledMatrix data.aMatrix index)
        (sampledMatrix data.bMatrix index) row column := by
  unfold synchronizedPeriodPairingResidual
  rw [GeometricApproximation.sub_sample,
    ScaledInverseCertificate.geometricProductEntry_sample, ScaledInverseCertificate.geometricProductEntry_sample,
    Multiplication.mul_apply,
    Multiplication.mul_apply,
    Stokes.symplecticPairing,
    ← FiniteSum.Fin.sumFin_sub]
  apply FiniteSum.Fin.sumFin_congr
  intro cycle
  simp only [
    Matrix.sampleMatrix_apply,
    ScaledInverseCertificate.geometricTranspose_apply, geometricMatrixOfNamed_apply,
    GeometricApproximation.ofNamed_sample,
    sampledMatrix_apply, -eq_self, -iff_self]
  rfl

/-- The actual stateful matrix expression realizes the synchronized finite symplectic pairing stream. This is the
operational bridge from persistent period programs to exact polygon algebra. -/
@[expose] def periodPairingResidual_equivalent_synchronized {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent (periodPairingResidual data row
      column).name
      (geometricNamed
        (synchronizedPeriodPairingResidual data row column)).name := by
  let aSource := geometricMatrixOfNamed data.aMatrix
  let bSource := geometricMatrixOfNamed data.bMatrix
  let left := matrixMul data.aMatrix (transpose data.bMatrix) row column
  let right := matrixMul data.bMatrix (transpose data.aMatrix) row column
  let leftSource := ScaledInverseCertificate.geometricProductEntry aSource
    (ScaledInverseCertificate.geometricTranspose bSource) row column
  let rightSource := ScaledInverseCertificate.geometricProductEntry bSource
    (ScaledInverseCertificate.geometricTranspose aSource) row column
  have leftEquivalent : Gaussian.Equivalence.NamedEquivalent left.name
      (geometricNamed leftSource).name := by
    exact ScaledInverseCertificate.matrixMul_equivalent_geometricProduct
      data.aMatrix (transpose data.bMatrix)
      aSource (ScaledInverseCertificate.geometricTranspose bSource)
      (fun matrixRow matrixColumn => by
        simpa only [aSource, geometricMatrixOfNamed_apply] using
          ScaledInverseCertificate.named_equivalent_geometricOfNamed
            (data.aMatrix matrixRow matrixColumn))
      (fun matrixRow matrixColumn => by
        simpa only [transpose_apply, ScaledInverseCertificate.geometricTranspose_apply, bSource,
          geometricMatrixOfNamed_apply] using
          ScaledInverseCertificate.named_equivalent_geometricOfNamed
            (data.bMatrix matrixColumn matrixRow))
      row column
  have rightEquivalent : Gaussian.Equivalence.NamedEquivalent right.name
      (geometricNamed rightSource).name := by
    exact ScaledInverseCertificate.matrixMul_equivalent_geometricProduct
      data.bMatrix (transpose data.aMatrix)
      bSource (ScaledInverseCertificate.geometricTranspose aSource)
      (fun matrixRow matrixColumn => by
        simpa only [bSource, geometricMatrixOfNamed_apply] using
          ScaledInverseCertificate.named_equivalent_geometricOfNamed
            (data.bMatrix matrixRow matrixColumn))
      (fun matrixRow matrixColumn => by
        simpa only [transpose_apply, ScaledInverseCertificate.geometricTranspose_apply, aSource,
          geometricMatrixOfNamed_apply] using
          ScaledInverseCertificate.named_equivalent_geometricOfNamed
            (data.aMatrix matrixColumn matrixRow))
      row column
  have negativeEquivalent := Comparison.coherentNeg_equivalent_geometricNeg
    right rightSource rightEquivalent
  simpa only [periodPairingResidual,
    synchronizedPeriodPairingResidual,
    left, right, leftSource, rightSource, aSource, bSource,
    GeometricApproximation.sub] using
    Comparison.coherentAdd_equivalent_geometricAdd
      left (neg right)
      leftSource
      (GeometricApproximation.neg
        rightSource)
      leftEquivalent negativeEquivalent

/-- Synchronized doubled cut-polygon boundary stream. The factor two keeps all face and edge identities division-free.
-/
@[expose] def synchronizedPeriodPolygonBoundary {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    Gaussian.Geometric.GeometricApproximation :=
  GeometricApproximation.mul
    (GeometricApproximation.exact 2)
    (synchronizedPeriodPairingResidual data row column)

/-- At every finite refinement, the synchronized boundary stream is the literal exact boundary area of all displayed
handle commutator polygons. -/
@[simp] theorem synchronizedPeriodPolygonBoundary_sample {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) (index : Nat) :
    (synchronizedPeriodPolygonBoundary data row column).sample index =
      Stokes.symplecticBoundaryArea
        (sampledMatrix data.aMatrix index)
        (sampledMatrix data.bMatrix index) row column := by
  rw [synchronizedPeriodPolygonBoundary,
    GeometricApproximation.mul_sample,
    GeometricApproximation.exact_sample,
    synchronizedPeriodPairingResidual_sample,
    Stokes.symplecticBoundaryArea_eq_two_mul_pairing]

/-- The stateful doubled residual and the exact synchronized polygon boundary are the same operational finite object. -/
@[expose] def doubledPeriodPairingResidual_equivalent_polygonBoundary {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent
      (mul
        (Coherence.exact 2)
        (periodPairingResidual data row column)).name
      (geometricNamed
        (synchronizedPeriodPolygonBoundary data row column)).name := by
  simpa only [synchronizedPeriodPolygonBoundary] using
    ScaledInverseCertificate.coherentMul_equivalent_geometricMul
      (Coherence.exact 2)
      (periodPairingResidual data row column)
      (GeometricApproximation.exact 2)
      (synchronizedPeriodPairingResidual data row column)
      (NamedEquivalent.symm
        (Comparison.geometricExact_equivalent_exact 2))
      (periodPairingResidual_equivalent_synchronized data row column)

/-- One displayed symplectic-cycle contribution `Aᵢₖ Bⱼₖ - Bᵢₖ Aⱼₖ` to the first bilinear relation. -/
@[expose] def periodPairingCycleTerm {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) : Coherent.CoherentNamed :=
  add
    (mul
      (data.aMatrix row cycle) (data.bMatrix column cycle))
    (neg
      (mul
        (data.bMatrix row cycle) (data.aMatrix column cycle)))

/-- Synchronized finite program for the positive product `Aᵢₖ Bⱼₖ` in one symplectic-cycle contribution. -/
@[expose] def periodPairingLeftProductProgram {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) : RefinementProgram :=
  RefinementProgram.multiply
    (data.aProgram row cycle).integral
    (data.bProgram column cycle).integral

/-- Synchronized finite program for the negative-side product `Bᵢₖ Aⱼₖ` in one symplectic-cycle contribution. -/
@[expose] def periodPairingRightProductProgram {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) : RefinementProgram :=
  RefinementProgram.multiply
    (data.bProgram row cycle).integral
    (data.aProgram column cycle).integral

/-- Arithmetic value assembled from the two explicit synchronized product programs. -/
@[expose] def periodPairingCycleProgramValue {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) : Coherent.CoherentNamed :=
  add
    (periodPairingLeftProductProgram data row column cycle).output
    (neg
      (periodPairingRightProductProgram data row column cycle).output)

/-- One actual finite refinement program for the antisymmetric cycle term. Its samples come from the displayed
arithmetic CCL rather than from an unstructured convergence field. -/
@[expose] def periodPairingCycleProgram {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) : RefinementProgram :=
  RefinementProgram.ofCoherentNamed
    (periodPairingCycleProgramValue data row column cycle)

/-- The original A-row/B-column product is operationally equivalent to the output of its retained synchronized product
program. -/
@[expose] def periodPairingLeftProduct_equivalent {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent
      (mul
        (data.aMatrix row cycle) (data.bMatrix column cycle)).name
      (periodPairingLeftProductProgram data row column cycle).output.name := by
  simpa only [periodPairingLeftProductProgram, PeriodData.aMatrix_apply,
    PeriodData.bMatrix_apply, CertifiedPeriodProgram.output,
    CertifiedPeriodProgram.toPeriodProgram,
    PeriodProgram.output] using
    Comparison.multiplyProgram_output_equivalent
      (data.aProgram row cycle).integral
      (data.bProgram column cycle).integral

/-- The original B-row/A-column product is operationally equivalent to the output of its retained synchronized product
program. -/
@[expose] def periodPairingRightProduct_equivalent {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent
      (mul
        (data.bMatrix row cycle) (data.aMatrix column cycle)).name
      (periodPairingRightProductProgram data row column cycle).output.name := by
  simpa only [periodPairingRightProductProgram, PeriodData.aMatrix_apply,
    PeriodData.bMatrix_apply, CertifiedPeriodProgram.output,
    CertifiedPeriodProgram.toPeriodProgram,
    PeriodProgram.output] using
    Comparison.multiplyProgram_output_equivalent
      (data.bProgram row cycle).integral
      (data.aProgram column cycle).integral

/-- The original period-matrix expression is operationally represented by the arithmetic value built from its two
explicit product programs. -/
@[expose] def periodPairingCycleTerm_equivalent_programValue {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent (periodPairingCycleTerm data row column
      cycle).name
      (periodPairingCycleProgramValue data row column cycle).name := by
  let leftOriginal := mul
    (data.aMatrix row cycle) (data.bMatrix column cycle)
  let rightOriginal := mul
    (data.bMatrix row cycle) (data.aMatrix column cycle)
  let leftProgram := periodPairingLeftProductProgram data row column cycle
  let rightProgram := periodPairingRightProductProgram data row column cycle
  have leftEquivalent : Gaussian.Equivalence.NamedEquivalent leftOriginal.name
      leftProgram.output.name := by
    simpa only [leftOriginal, leftProgram] using
      periodPairingLeftProduct_equivalent data row column cycle
  have rightEquivalent : Gaussian.Equivalence.NamedEquivalent rightOriginal.name
      rightProgram.output.name := by
    simpa only [rightOriginal, rightProgram] using
      periodPairingRightProduct_equivalent data row column cycle
  have negativeEquivalent := Additive.coherentNeg_respects rightOriginal
    rightProgram.output rightEquivalent
  simpa only [periodPairingCycleTerm,
    periodPairingCycleProgramValue,
    leftOriginal, rightOriginal, leftProgram, rightProgram,
    CoherentNamed.add,
    CoherentNamed.neg] using
    Congruence.coherentAdd_respects
      leftOriginal leftProgram.output
      (neg rightOriginal)
      (neg rightProgram.output)
      leftEquivalent negativeEquivalent

/-- Each antisymmetric cycle contribution is now backed by one explicit finite refinement program suitable for primitive
or paired Stokes boundaries. -/
@[expose] def periodPairingCycleTerm_equivalent_program {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent (periodPairingCycleTerm data row column
      cycle).name
      (periodPairingCycleProgram data row column cycle).output.name :=
  NamedEquivalent.trans
    (periodPairingCycleTerm_equivalent_programValue data row column cycle)
    (Comparison.ofCoherentNamed_output_equivalent
      (periodPairingCycleProgramValue data row column cycle))

/-- The direct finite sum of all symplectic-cycle contributions. -/
@[expose] def periodPairingCycleSum {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    Coherent.CoherentNamed :=
  sumNamed fun cycle => periodPairingCycleTerm data row column cycle

/-- Finite recursive sum of the explicit cycle-term program outputs. -/
@[expose] def periodPairingCycleProgramSumValue {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) : Coherent.CoherentNamed :=
  sumNamed fun cycle => (periodPairingCycleProgram data row column
    cycle).output

/-- One finite refinement program carrying the complete antisymmetric symplectic-cycle sum. -/
@[expose] def periodPairingCycleSumProgram {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) : RefinementProgram :=
  RefinementProgram.ofCoherentNamed
    (periodPairingCycleProgramSumValue data row column)

/-- Termwise product-program correctness lifts through the finite recursive cycle sum. -/
@[expose] def periodPairingCycleSum_equivalent_programValue {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent (periodPairingCycleSum data row
      column).name
      (periodPairingCycleProgramSumValue data row column).name := by
  unfold periodPairingCycleSum
    periodPairingCycleProgramSumValue
  exact sumNamed_respects
    (fun cycle => periodPairingCycleTerm data row column cycle)
    (fun cycle => (periodPairingCycleProgram data row column cycle).output)
    (fun cycle =>
      periodPairingCycleTerm_equivalent_program data row column cycle)

/-- The complete first-relation cycle sum is represented by one actual finite Gaussian refinement program. -/
@[expose] def periodPairingCycleSum_equivalent_program {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent (periodPairingCycleSum data row
      column).name
      (periodPairingCycleSumProgram data row column).output.name :=
  NamedEquivalent.trans
    (periodPairingCycleSum_equivalent_programValue data row column)
    (Comparison.ofCoherentNamed_output_equivalent
      (periodPairingCycleProgramSumValue data row column))

/-- Endpoint reached by cumulatively adjoining all explicit cycle-term programs, starting from exact zero. -/
@[expose] def periodPairingPrimitiveFinish {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) : Coherent.CoherentNamed :=
  Primitive.cumulativePrimitiveFinish
    (Coherence.exact 0)
    (fun cycle => periodPairingCycleProgram data row column cycle)

/-- Canonical primitive path whose edges are precisely the finite programs for the antisymmetric symplectic-cycle terms.
-/
@[expose] def periodPairingPrimitivePath {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    Primitive.PrimitivePath (Coherence.exact 0)
      (periodPairingPrimitiveFinish data row column) :=
  Primitive.cumulativePrimitivePath
    (Coherence.exact 0)
    (fun cycle => periodPairingCycleProgram data row column cycle)

/-- The canonical accumulated primitive endpoint is represented by the one explicit refinement program carrying the
complete synchronized cycle sum. -/
@[expose] def periodPairingPrimitiveFinish_equivalent_program {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent (periodPairingPrimitiveFinish data row
      column).name
      (periodPairingCycleSumProgram data row column).output.name := by
  apply NamedEquivalent.trans
    (Primitive.cumulativePrimitiveFinish_zero_equivalent_sumNamed
      (fun cycle => periodPairingCycleProgram data row column cycle))
  simpa only [periodPairingCycleSumProgram,
    periodPairingCycleProgramSumValue] using
    Comparison.ofCoherentNamed_output_equivalent
      (periodPairingCycleProgramSumValue data row column)

set_option genInjectivity false in
/-- The only closure datum needed by the canonical finite Stokes boundary: the explicitly accumulated cycle-term
primitive returns operationally to its displayed starting zero. Edge programs, endpoints, FTC identities, and the
comparison with the period matrix are all derived. -/
structure StokesClosure {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (data : PeriodData curve) where
  /-- For each original differential pair, the accumulated canonical cycle primitive returns operationally to its exact
    starting zero. -/ closed : forall row column : Fin genus,
    Gaussian.Equivalence.NamedEquivalent (periodPairingPrimitiveFinish data row
      column).name
      (Coherence.exact 0).name

constructive_injectivity StokesClosure

namespace StokesClosure

/-- Materialize the canonical closed primitive boundary for one pair of differentials. -/
@[expose] def boundary {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve} (closure : StokesClosure data)
    (row column : Fin genus) : Primitive.ClosedPrimitiveBoundary where
  start := Coherence.exact 0
  finish := periodPairingPrimitiveFinish data row column
  path := periodPairingPrimitivePath data row column
  closed := closure.closed row column

/-- The original period-pairing cycle sum is automatically identified with the integral sum of the canonical primitive
boundary. -/
@[expose] def cycleSum_eq_boundary {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve} (closure : StokesClosure data)
    (row column : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent (periodPairingCycleSum data row
      column).name
      (closure.boundary row column).integralSum.name := by
  apply NamedEquivalent.trans
    (periodPairingCycleSum_equivalent_programValue data row column)
  apply NamedEquivalent.symm
  change Gaussian.Equivalence.NamedEquivalent
    (Primitive.cumulativePrimitivePath
      (Coherence.exact 0)
      (fun cycle => periodPairingCycleProgram data row column
        cycle)).integralSum.name
    (sumNamed fun cycle =>
      (periodPairingCycleProgram data row column cycle).output).name
  exact Primitive.cumulativePrimitivePath_integralSum_equivalent_sumNamed
    (Coherence.exact 0)
    (fun cycle => periodPairingCycleProgram data row column cycle)

end StokesClosure

/-- Matrix notation for `A Bᵀ - B Aᵀ` is operationally the explicit finite sum of the displayed cycle-pairing terms. -/
@[expose] def periodPairingResidual_equivalent_cycleSum {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent (periodPairingResidual data row
      column).name
      (periodPairingCycleSum data row column).name := by
  let leftTerms := fun cycle : Fin genus =>
    mul
      (data.aMatrix row cycle) (data.bMatrix column cycle)
  let rightTerms := fun cycle : Fin genus =>
    mul
      (data.bMatrix row cycle) (data.aMatrix column cycle)
  let negativeRightTerms := fun cycle : Fin genus =>
    neg (rightTerms cycle)
  have splitTerms : Gaussian.Equivalence.NamedEquivalent
      (periodPairingCycleSum data row column).name
      (add
        (sumNamed leftTerms) (sumNamed negativeRightTerms)).name := by
    change Gaussian.Equivalence.NamedEquivalent
      (sumNamed fun cycle =>
        add
          (leftTerms cycle) (negativeRightTerms cycle)).name
      (add
        (sumNamed leftTerms) (sumNamed negativeRightTerms)).name
    exact FiniteSum.sumNamed_add leftTerms negativeRightTerms
  have collectNegative : Gaussian.Equivalence.NamedEquivalent
      (add
        (sumNamed leftTerms) (sumNamed negativeRightTerms)).name
      (add
        (sumNamed leftTerms)
        (neg
          (sumNamed rightTerms))).name :=
    Congruence.coherentAdd_respects
      (sumNamed leftTerms) (sumNamed leftTerms)
      (sumNamed negativeRightTerms)
      (neg (sumNamed rightTerms))
      (NamedEquivalent.refl _)
      (by
        change Gaussian.Equivalence.NamedEquivalent
          (sumNamed fun cycle =>
            neg
              (rightTerms cycle)).name
          (neg
            (sumNamed rightTerms)).name
        exact FiniteSum.sumNamed_neg rightTerms)
  have leftEquivalent : Gaussian.Equivalence.NamedEquivalent
      (matrixMul data.aMatrix (transpose data.bMatrix) row column).name
      (sumNamed leftTerms).name := by
    rw [matrixMul_apply]
    apply sumNamed_respects
    intro cycle
    unfold leftTerms
    rw [transpose_apply]
    exact NamedEquivalent.refl _
  have rightEquivalent : Gaussian.Equivalence.NamedEquivalent
      (matrixMul data.bMatrix (transpose data.aMatrix) row column).name
      (sumNamed rightTerms).name := by
    rw [matrixMul_apply]
    apply sumNamed_respects
    intro cycle
    unfold rightTerms
    rw [transpose_apply]
    exact NamedEquivalent.refl _
  have residualEquivalent : Gaussian.Equivalence.NamedEquivalent
      (periodPairingResidual data row column).name
      (add
        (sumNamed leftTerms)
        (neg
          (sumNamed rightTerms))).name := by
    unfold periodPairingResidual
    exact Congruence.coherentAdd_respects
      (matrixMul data.aMatrix (transpose data.bMatrix) row column)
      (sumNamed leftTerms)
      (neg
        (matrixMul data.bMatrix (transpose data.aMatrix) row column))
      (neg (sumNamed rightTerms))
      leftEquivalent
      (Additive.coherentNeg_respects
        (matrixMul data.bMatrix (transpose data.aMatrix) row column)
        (sumNamed rightTerms) rightEquivalent)
  exact NamedEquivalent.trans residualEquivalent
    (NamedEquivalent.symm
      (NamedEquivalent.trans splitTerms
        collectNegative))

/-- The sampled antisymmetric cycle sum and the synchronized geometric residual are two finite operational presentations
of the same value. This ties the first-relation interface to the geometric object that the cut-surface comparisons
bound. -/
@[expose] def periodPairingCycleSum_equivalent_synchronized {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent (periodPairingCycleSum data row
      column).name
      (geometricNamed
        (synchronizedPeriodPairingResidual data row column)).name :=
  NamedEquivalent.trans
    (NamedEquivalent.symm
      (periodPairingResidual_equivalent_cycleSum data row column))
    (periodPairingResidual_equivalent_synchronized data row column)

/-- The unnormalized first-relation residual is operationally skew-symmetric. This is proved directly from the two
finite matrix-product sums and stateful commutativity of each displayed product. -/
@[expose] def periodPairingResidual_swap {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent (periodPairingResidual data column
      row).name
      (neg
        (periodPairingResidual data row column)).name := by
  let left := matrixMul data.aMatrix (transpose data.bMatrix) row column
  let right := matrixMul data.bMatrix (transpose data.aMatrix) row column
  let swappedLeft :=
    matrixMul data.aMatrix (transpose data.bMatrix) column row
  let swappedRight :=
    matrixMul data.bMatrix (transpose data.aMatrix) column row
  have swappedLeft_eq_right : Gaussian.Equivalence.NamedEquivalent swappedLeft.name right.name := by
    unfold swappedLeft right
    rw [matrixMul_apply, matrixMul_apply]
    apply sumNamed_respects
    intro cycle
    rw [transpose_apply, transpose_apply]
    exact Laws.coherentMul_comm
      (data.aMatrix column cycle) (data.bMatrix row cycle)
  have swappedRight_eq_left : Gaussian.Equivalence.NamedEquivalent swappedRight.name left.name := by
    unfold swappedRight left
    rw [matrixMul_apply, matrixMul_apply]
    apply sumNamed_respects
    intro cycle
    rw [transpose_apply, transpose_apply]
    exact Laws.coherentMul_comm
      (data.bMatrix column cycle) (data.aMatrix row cycle)
  have replaceBoth : Gaussian.Equivalence.NamedEquivalent
      (add swappedLeft
        (neg swappedRight)).name
      (add right
        (neg left)).name :=
    Congruence.coherentAdd_respects
      swappedLeft right
      (neg swappedRight)
      (neg left)
      swappedLeft_eq_right
      (Additive.coherentNeg_respects swappedRight left swappedRight_eq_left)
  have residualReplace : Gaussian.Equivalence.NamedEquivalent
      (periodPairingResidual data column row).name
      (add right
        (neg left)).name := by
    unfold periodPairingResidual
    change Gaussian.Equivalence.NamedEquivalent
      (add swappedLeft
        (neg swappedRight)).name
      (add right
        (neg left)).name
    exact replaceBoth
  exact NamedEquivalent.trans
    residualReplace
    (Additive.coherentSub_swap left right)

/-- The canonical primitive endpoint and the matrix-form first-relation residual are two finite operational
presentations of the same value. -/
@[expose] def periodPairingPrimitiveFinish_equivalent_residual {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent (periodPairingPrimitiveFinish data row
      column).name
      (periodPairingResidual data row column).name :=
  NamedEquivalent.trans
    (Primitive.cumulativePrimitiveFinish_zero_equivalent_sumNamed
      (fun cycle => periodPairingCycleProgram data row column cycle))
    (NamedEquivalent.trans
      (NamedEquivalent.symm
        (periodPairingCycleSum_equivalent_programValue data row column))
      (NamedEquivalent.symm
        (periodPairingResidual_equivalent_cycleSum data row column)))

/-- Swapping the two differential indices negates the accumulated canonical Stokes primitive. -/
@[expose] def periodPairingPrimitiveFinish_swap {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent (periodPairingPrimitiveFinish data column
      row).name
      (neg
        (periodPairingPrimitiveFinish data row column)).name :=
  NamedEquivalent.trans
    (periodPairingPrimitiveFinish_equivalent_residual data column row)
    (NamedEquivalent.trans
      (periodPairingResidual_swap data row column)
      (Additive.coherentNeg_respects
        (periodPairingResidual data row column)
        (periodPairingPrimitiveFinish data row column)
        (NamedEquivalent.symm
          (periodPairingPrimitiveFinish_equivalent_residual data row column))))

namespace StokesClosure

/-- On the diagonal the two finite matrix-product sums agree term by term by operational commutativity, so the
unnormalized antisymmetric residual is zero. -/
@[expose] def periodPairingResidual_diagonal_zero {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent (periodPairingResidual data row
      row).name
      (Coherence.exact 0).name := by
  let left := matrixMul data.aMatrix (transpose data.bMatrix) row row
  let right := matrixMul data.bMatrix (transpose data.aMatrix) row row
  have products : Gaussian.Equivalence.NamedEquivalent left.name right.name := by
    unfold left right
    rw [matrixMul_apply, matrixMul_apply]
    apply sumNamed_respects
    intro cycle
    rw [transpose_apply, transpose_apply]
    exact Laws.coherentMul_comm
      (data.aMatrix row cycle) (data.bMatrix row cycle)
  have replaceLeft : Gaussian.Equivalence.NamedEquivalent
      (add left
        (neg right)).name
      (add right
        (neg right)).name :=
    Congruence.coherentAdd_respects
      left right
      (neg right)
      (neg right)
      products (NamedEquivalent.refl _)
  have cancelRight : Gaussian.Equivalence.NamedEquivalent
      (add right
        (neg right)).name
      (Coherence.exact 0).name := by
    simpa only [CoherentNamed.add,
      CoherentNamed.neg,
      Coherence.exact] using
      Neg.coherentAdd_neg_right right
  have residualReplace : Gaussian.Equivalence.NamedEquivalent
      (periodPairingResidual data row row).name
      (add right
        (neg right)).name := by
    unfold periodPairingResidual
    change Gaussian.Equivalence.NamedEquivalent
      (add left
        (neg right)).name
      (add right
        (neg right)).name
    exact replaceLeft
  exact NamedEquivalent.trans
    residualReplace
    cancelRight

/-- The canonical primitive used by the finite Stokes interface therefore closes automatically on every diagonal entry.
The proof passes through the actual synchronized product programs, rather than replacing their outputs by an untracked
algebraic expression. -/
@[expose] def periodPairingPrimitiveFinish_diagonal_zero {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row : Fin genus) :
    Gaussian.Equivalence.NamedEquivalent (periodPairingPrimitiveFinish data row
      row).name
      (Coherence.exact 0).name :=
  NamedEquivalent.trans
    (Primitive.cumulativePrimitiveFinish_zero_equivalent_sumNamed
      (fun cycle => periodPairingCycleProgram data row row cycle))
    (NamedEquivalent.trans
      (NamedEquivalent.symm
        (periodPairingCycleSum_equivalent_programValue data row row))
      (NamedEquivalent.trans
        (NamedEquivalent.symm
          (periodPairingResidual_equivalent_cycleSum data row row))
        (periodPairingResidual_diagonal_zero data row)))

/-- If the finite differential index has at most one member, every entry is diagonal and the complete finite Stokes
closure is constructed without a surface-boundary certificate. -/
@[expose] def ofSubsingleton {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (allEqual : forall row column : Fin genus, row = column) :
    StokesClosure data where
  closed := by
    intro row column
    cases allEqual row column
    exact periodPairingPrimitiveFinish_diagonal_zero data row

/-- In genus one the first Riemann bilinear relation needs no separately supplied Stokes datum: the sole matrix entry is
diagonal. -/
@[expose] def genusOne {curve : Basic.HyperellipticCurve 1} (data : PeriodData curve) :
    StokesClosure data :=
  ofSubsingleton data (by
    intro row column
    rcases row with ⟨row, rowBound⟩
    rcases column with ⟨column, columnBound⟩
    cases row with
    | zero =>
      cases column with
      | zero => rfl
      | succ column =>
        exact False.elim (Nat.not_lt_zero column (Nat.lt_of_succ_lt_succ columnBound))
    | succ row =>
      exact False.elim (Nat.not_lt_zero row (Nat.lt_of_succ_lt_succ rowBound)))

end StokesClosure

set_option genInjectivity false in
/-- Minimal independent first-relation data: diagonal entries are automatic, and skew-symmetry reconstructs the lower
triangle, so only strict upper-triangular primitive closures are supplied. -/
structure UpperTriangularStokesClosure {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (data : PeriodData curve) where
  /-- For each strictly ordered differential pair, the original accumulated canonical cycle primitive is operationally
    zero. -/ closed_of_lt : forall row column : Fin genus, row.val < column.val ->
    Gaussian.Equivalence.NamedEquivalent (periodPairingPrimitiveFinish data row
      column).name
      (Coherence.exact 0).name

constructive_injectivity UpperTriangularStokesClosure

namespace UpperTriangularStokesClosure

/-- The complete strict-upper first bilinear relation follows from the single geometric vanishing of the sampled
antisymmetric cycle sum on each strict-upper differential pair. This isolates the remaining geometric obligation: the
named `periodPairingCycleSum` value must be operationally zero, and nothing else in the first-relation chain remains. -/
@[expose] def ofCycleSumZero {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (data : PeriodData curve)
    (zero_of_lt : forall row column : Fin genus, row.val < column.val ->
      Gaussian.Equivalence.NamedEquivalent (periodPairingCycleSum data row
        column).name
        (Coherence.exact 0).name) :
    UpperTriangularStokesClosure data where
  closed_of_lt := by
    intro row column less
    exact NamedEquivalent.trans
      (periodPairingPrimitiveFinish_equivalent_residual data row column)
      (NamedEquivalent.trans
        (periodPairingResidual_equivalent_cycleSum data row column)
        (zero_of_lt row column less))

/-- The complete strict-upper first bilinear relation from the geometric vanishing of the synchronized residual itself.
This is the form the cut-surface comparisons produce: `synchronizedPeriodPairingResidual` is the synchronized
`GeometricApproximation` whose samples are `Sum_c (A_{r,c}B_{k,c} - B_{r,c}A_{k,c})`. -/
@[expose] def ofSynchronizedZero {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (data : PeriodData curve)
    (zero_of_lt : forall row column : Fin genus, row.val < column.val ->
      Gaussian.Equivalence.NamedEquivalent
        (geometricNamed
          (synchronizedPeriodPairingResidual data row column)).name
        (Coherence.exact 0).name) :
    UpperTriangularStokesClosure data where
  closed_of_lt := by
    intro row column less
    exact NamedEquivalent.trans
      (periodPairingPrimitiveFinish_equivalent_residual data row column)
      (NamedEquivalent.trans
        (periodPairingResidual_equivalent_cycleSum data row column)
        (NamedEquivalent.trans
          (periodPairingCycleSum_equivalent_synchronized data row column)
          (zero_of_lt row column less)))

/-- Reconstruct the complete finite Stokes closure from exactly its independent upper-triangular entries. -/
@[expose] def toStokesClosure {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    (upper : UpperTriangularStokesClosure data) :
    StokesClosure data where
  closed := by
    intro row column
    by_cases equal : row = column
    · subst column
      exact StokesClosure.periodPairingPrimitiveFinish_diagonal_zero
        data row
    · by_cases less : row.val < column.val
      · exact upper.closed_of_lt row column less
      · have reverseLess : column.val < row.val := by
          have differentValues : row.val ≠ column.val := by
            intro valuesEqual
            exact equal (Fin.ext valuesEqual)
          omega0
        have reverseZero := upper.closed_of_lt column row reverseLess
        exact NamedEquivalent.trans
          (periodPairingPrimitiveFinish_swap data column row)
          (NamedEquivalent.trans
            (Additive.coherentNeg_respects
              (periodPairingPrimitiveFinish data column row)
              (Coherence.exact 0)
              reverseZero)
            (NamedEquivalent.symm
              Additive.zero_equivalent_neg_zero))

/-- In genus two there is exactly one independent first-relation equation, the `(0,1)` entry. -/
@[expose] def genusTwo {curve : Basic.HyperellipticCurve 2} (data : PeriodData curve)
    (zeroOne : Gaussian.Equivalence.NamedEquivalent
      (periodPairingPrimitiveFinish data 0 1).name
      (Coherence.exact 0).name) :
    UpperTriangularStokesClosure data where
  closed_of_lt := by
    intro row column less
    have rowZero : row = (⟨0, by decide⟩ : Fin 2) := by
      apply Fin.ext
      change row.val = 0
      have bound := column.isLt
      omega0
    have columnOne : column = (⟨1, by decide⟩ : Fin 2) := by
      apply Fin.ext
      change column.val = 1
      have bound := row.isLt
      omega0
    subst row
    subst column
    exact zeroOne

end UpperTriangularStokesClosure

namespace StokesClosure

/-- One off-diagonal surface calculation closes the complete genus-two first bilinear relation. -/
@[expose] def genusTwo_of_zeroOne {curve : Basic.HyperellipticCurve 2}
    (data : PeriodData curve)
    (zeroOne : Gaussian.Equivalence.NamedEquivalent
      (periodPairingPrimitiveFinish data 0 1).name
      (Coherence.exact 0).name) :
    StokesClosure data :=
  (UpperTriangularStokesClosure.genusTwo data zeroOne).toStokesClosure

end StokesClosure

end Purelib.Curves.Hyperelliptic.Periods.Pairing

end
