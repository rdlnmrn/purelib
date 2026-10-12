module
public import Purelib.Approximation.Gaussian.Division.Cancellation
public import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Approximation.Gaussian.Equivalence
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Data.Vector.Basic

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.PeriodMatrix

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

namespace Purelib.Approximation.Matrix.Operational.Bilinear

/-- The canonical adjugate turns the unnormalized first bilinear relation `A Bᵀ = B Aᵀ` into symmetry of `adj(A) B`. The
argument is entirely finite: the relation is sandwiched by `adj(A)` and its transpose, both scaled-inverse identities
are operational theorems, and the apart scalar is cancelled by its productive reciprocal. -/
def numeratorMatrix_symmetric_of_periodRelation {size : Nat}
    (a b : PeriodMatrix.NamedMatrix size) (inverse : PeriodMatrix.ScaledInverseCertificate a)
    (periodRelation : PeriodMatrix.MatrixEquivalent
      (PeriodMatrix.matrixMul a (PeriodMatrix.transpose b))
      (PeriodMatrix.matrixMul b (PeriodMatrix.transpose a))) :
    PeriodMatrix.MatrixEquivalent (PeriodMatrix.matrixMul inverse.adjugate b)
      (PeriodMatrix.transpose (PeriodMatrix.matrixMul inverse.adjugate b)) := by
  let c := inverse.adjugate
  let scalar := inverse.scalar
  let n := PeriodMatrix.matrixMul c b
  let aBt := PeriodMatrix.matrixMul a (PeriodMatrix.transpose b)
  let bAt := PeriodMatrix.matrixMul b (PeriodMatrix.transpose a)
  let cTranspose := PeriodMatrix.transpose c
  let leftSandwich := PeriodMatrix.matrixMul (PeriodMatrix.matrixMul c aBt) cTranspose
  let rightSandwich := PeriodMatrix.matrixMul (PeriodMatrix.matrixMul c bAt) cTranspose
  have cRefl : PeriodMatrix.MatrixEquivalent c c := MatrixEquivalent.refl c
  have cTransposeRefl : PeriodMatrix.MatrixEquivalent cTranspose cTranspose :=
    MatrixEquivalent.refl cTranspose
  have sandwichedRelation : PeriodMatrix.MatrixEquivalent leftSandwich rightSandwich := by
    have leftMultiply : PeriodMatrix.MatrixEquivalent
        (PeriodMatrix.matrixMul c aBt) (PeriodMatrix.matrixMul c bAt) :=
      PeriodMatrix.matrixMul_respects c c aBt bAt cRefl (by
        simpa only [aBt, bAt] using periodRelation)
    exact PeriodMatrix.matrixMul_respects
      (PeriodMatrix.matrixMul c aBt) (PeriodMatrix.matrixMul c bAt)
      cTranspose cTranspose leftMultiply cTransposeRefl
  have caScaled : PeriodMatrix.MatrixEquivalent (PeriodMatrix.matrixMul c a)
      (PeriodMatrix.scaleIdentity scalar) := by
    intro row column
    simpa only [c, scalar] using inverse.left_identity row column
  have bTranspose_cTranspose : PeriodMatrix.MatrixEquivalent
      (PeriodMatrix.matrixMul (PeriodMatrix.transpose b) cTranspose) (PeriodMatrix.transpose n) := by
    exact MatrixEquivalent.symm (by
      simpa only [cTranspose, n, c] using ScaledInverseCertificate.matrixMul_transpose c b)
  have leftReduction : PeriodMatrix.MatrixEquivalent leftSandwich
      (ScaledInverseCertificate.scalarMul scalar (PeriodMatrix.transpose n)) := by
    have exposeCA : PeriodMatrix.MatrixEquivalent
        (PeriodMatrix.matrixMul c aBt)
        (PeriodMatrix.matrixMul (PeriodMatrix.matrixMul c a) (PeriodMatrix.transpose b)) :=
      MatrixEquivalent.symm (by
        simpa only [aBt] using ScaledInverseCertificate.matrixMul_assoc c a (PeriodMatrix.transpose b))
    have exposeCAInside : PeriodMatrix.MatrixEquivalent leftSandwich
        (PeriodMatrix.matrixMul (PeriodMatrix.matrixMul (PeriodMatrix.matrixMul c a) (PeriodMatrix.transpose b))
          cTranspose) := by
      exact PeriodMatrix.matrixMul_respects
        (PeriodMatrix.matrixMul c aBt)
        (PeriodMatrix.matrixMul (PeriodMatrix.matrixMul c a) (PeriodMatrix.transpose b))
        cTranspose cTranspose exposeCA cTransposeRefl
    have associateRight : PeriodMatrix.MatrixEquivalent
        (PeriodMatrix.matrixMul (PeriodMatrix.matrixMul (PeriodMatrix.matrixMul c a) (PeriodMatrix.transpose b))
          cTranspose)
        (PeriodMatrix.matrixMul (PeriodMatrix.matrixMul c a)
          (PeriodMatrix.matrixMul (PeriodMatrix.transpose b) cTranspose)) :=
      ScaledInverseCertificate.matrixMul_assoc (PeriodMatrix.matrixMul c a) (PeriodMatrix.transpose b) cTranspose
    have replaceFactors : PeriodMatrix.MatrixEquivalent
        (PeriodMatrix.matrixMul (PeriodMatrix.matrixMul c a)
          (PeriodMatrix.matrixMul (PeriodMatrix.transpose b) cTranspose))
        (PeriodMatrix.matrixMul (PeriodMatrix.scaleIdentity scalar) (PeriodMatrix.transpose n)) :=
      PeriodMatrix.matrixMul_respects (PeriodMatrix.matrixMul c a) (PeriodMatrix.scaleIdentity scalar)
        (PeriodMatrix.matrixMul (PeriodMatrix.transpose b) cTranspose) (PeriodMatrix.transpose n)
        caScaled bTranspose_cTranspose
    exact MatrixEquivalent.trans exposeCAInside
      (MatrixEquivalent.trans associateRight
        (MatrixEquivalent.trans replaceFactors
          (ScaledInverseCertificate.scaleIdentity_mul scalar (PeriodMatrix.transpose n))))
  have aTranspose_cTranspose_scaled : PeriodMatrix.MatrixEquivalent
      (PeriodMatrix.matrixMul (PeriodMatrix.transpose a) cTranspose) (PeriodMatrix.scaleIdentity scalar) := by
    have toTransposeCA : PeriodMatrix.MatrixEquivalent
        (PeriodMatrix.matrixMul (PeriodMatrix.transpose a) cTranspose) (PeriodMatrix.transpose (PeriodMatrix.matrixMul c
          a)) :=
      MatrixEquivalent.symm (by
        simpa only [cTranspose] using ScaledInverseCertificate.matrixMul_transpose c a)
    exact MatrixEquivalent.trans toTransposeCA
      (MatrixEquivalent.trans (PeriodMatrix.transpose_respects caScaled)
        (ScaledInverseCertificate.transpose_scaleIdentity scalar))
  have rightReduction : PeriodMatrix.MatrixEquivalent rightSandwich
      (ScaledInverseCertificate.scalarMul scalar n) := by
    have exposeCB : PeriodMatrix.MatrixEquivalent
        (PeriodMatrix.matrixMul c bAt)
        (PeriodMatrix.matrixMul n (PeriodMatrix.transpose a)) :=
      MatrixEquivalent.symm (by
        simpa only [bAt, n] using ScaledInverseCertificate.matrixMul_assoc c b (PeriodMatrix.transpose a))
    have exposeCBInside : PeriodMatrix.MatrixEquivalent rightSandwich
        (PeriodMatrix.matrixMul (PeriodMatrix.matrixMul n (PeriodMatrix.transpose a)) cTranspose) := by
      exact PeriodMatrix.matrixMul_respects
        (PeriodMatrix.matrixMul c bAt) (PeriodMatrix.matrixMul n (PeriodMatrix.transpose a))
        cTranspose cTranspose exposeCB cTransposeRefl
    have associateRight : PeriodMatrix.MatrixEquivalent
        (PeriodMatrix.matrixMul (PeriodMatrix.matrixMul n (PeriodMatrix.transpose a)) cTranspose)
        (PeriodMatrix.matrixMul n (PeriodMatrix.matrixMul (PeriodMatrix.transpose a) cTranspose)) :=
      ScaledInverseCertificate.matrixMul_assoc n (PeriodMatrix.transpose a) cTranspose
    have replaceFactor : PeriodMatrix.MatrixEquivalent
        (PeriodMatrix.matrixMul n (PeriodMatrix.matrixMul (PeriodMatrix.transpose a) cTranspose))
        (PeriodMatrix.matrixMul n (PeriodMatrix.scaleIdentity scalar)) :=
      PeriodMatrix.matrixMul_respects n n
        (PeriodMatrix.matrixMul (PeriodMatrix.transpose a) cTranspose) (PeriodMatrix.scaleIdentity scalar)
        (MatrixEquivalent.refl n) aTranspose_cTranspose_scaled
    exact MatrixEquivalent.trans exposeCBInside
      (MatrixEquivalent.trans associateRight
        (MatrixEquivalent.trans replaceFactor
          (ScaledInverseCertificate.matrixMul_scaleIdentity n scalar)))
  have scaledSymmetry : PeriodMatrix.MatrixEquivalent
      (ScaledInverseCertificate.scalarMul scalar (PeriodMatrix.transpose n)) (ScaledInverseCertificate.scalarMul scalar
        n) :=
    MatrixEquivalent.trans (MatrixEquivalent.symm leftReduction)
      (MatrixEquivalent.trans sandwichedRelation rightReduction)
  intro row column
  have scaledEntry := scaledSymmetry row column
  rw [ScaledInverseCertificate.scalarMul_apply, ScaledInverseCertificate.scalarMul_apply, PeriodMatrix.transpose_apply]
    at scaledEntry
  apply NamedEquivalent.symm
  simpa only [n, c, PeriodMatrix.transpose_apply] using
    Cancellation.coherentMul_cancel_left
      scalar (n column row) (n row column) inverse.scalarApart scaledEntry

end Purelib.Approximation.Matrix.Operational.Bilinear

end
