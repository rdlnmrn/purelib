module

public import Purelib.Riemann.Integration.PreparedConstantModels.Query
public import Purelib.Riemann.Branches.PreparedSheetContinuation.CachedSource.Transport
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
import Purelib.Riemann.RootContinuation.SquareRootProvenance.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Geometry.Rational.Box.Bounds

/-! # A retained physical query compared with an independently moving product

The actual direct-query Owner refines its unchanged cached prepared-source
box. The SAME already completed source comparison, actual prepared reading
and moving-product observation pay a signed sum floor on that query.
Square residual comparisons then derive its full-root agreement at the
identical physical point, without a supplied desired query relation.
-/

public section

namespace Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge.Query

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Branches.PreparedSheetContinuation (CachedSource)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {edge : PreparedEdge curve differential} {time : Rational} {inside : 0 ≤ time ∧ time ≤ 1}

/-- The actual retained original query agrees with a paid full product at that same physical point.

The existing source comparison is consumed unchanged. The old source and
prepared observations keep their actual radii and states. Refinement of the
actual query Owner pays its box diameter; the supplied movement is an
independently derived estimate on every candidate of the original product
state. The scalar payment selects the signed root, while its actual square
identity fixes the same radicand. No source comparison or root query is run
again by this constructor. The complete certificate of the SAME supplied
direct-query Owner and its whole original factory equality preserve the
actual value and square. The separate edge.sheetValue factory is neither
required nor executed.
-/
def productEquivalent (query : Query edge time inside)
    (queryRoot : CertifiedSquareRoot.Certificate (curve.polynomial.eval (edge.point time)))
    (queryRoot_eq : queryRoot = query.owner.certificate query.owner.parameterNonzero)
    {sourceChannel targetChannel : CoherentNamed}
    (sourceReading : Equivalence.Observation.Reading sourceChannel)
    (targetReading : Equivalence.Observation.Reading targetChannel)
    {root : CertifiedSquareRoot.Certificate (curve.polynomial.eval (edge.segment.pointAt edge.left.parameter))}
    (root_eq : root = edge.cached.preparedOwner.certificate edge.cached.preparedOwner.parameterNonzero)
    (preparedReading : Equivalence.Observation.Reading root.value) {comparisonTarget : Rational}
    (compared : Equivalence.Observation.Comparison sourceReading preparedReading comparisonTarget)
    (targetSquare : SquareRootProvenance.SquareIdentity targetChannel (curve.polynomial.eval (edge.point time)))
    (floor : Rational) (positive : 0 < floor)
    (sourceLower : floor ≤ Norm.Basic.normSq sourceReading.value) (movement : Rational)
    (targetMovement : ∀ {candidate : Canonical}, targetChannel.name.process.Possible targetReading.state candidate →
      Norm.Basic.normSq (sourceReading.value - candidate) ≤ movement)
    (payment : CachedSource.advancePayment sourceReading preparedReading comparisonTarget
      edge.cached.preparedOwner.track.initial.box.diagonalSq movement ≤ floor) :
    NamedEquivalent (edge.rootName time inside) targetChannel.name := by
  let targetBased := targetChannel.based targetReading.state
  have targetEquivalent := targetChannel.basedEquivalent targetReading.state
  have basedSquare : SquareRootProvenance.SquareIdentity targetBased (curve.polynomial.eval (edge.point time)) :=
    (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects targetBased targetChannel
      targetBased targetChannel targetEquivalent.symm targetEquivalent.symm).trans targetSquare
  have sourceClose := compared.reading_error_le
  have preparedInside := CertifiedSquareRoot.Sampling.candidate_in_initial_box edge.cached.preparedOwner
    root_eq preparedReading.possible
  have sumLower : ∀ leftIndex rightIndex,
      floor ≤ Canonical.normSq ((Name.Sampling.approximation queryRoot.value.name).sample leftIndex +
        (Name.Sampling.approximation targetBased.name).sample rightIndex) := by
    intro leftIndex rightIndex
    have actualPossible := Process.Sampling.witnessAt_possible queryRoot.value.name.process
      queryRoot.value.name.state leftIndex
    have commonInside : edge.cached.preparedOwner.track.initial.box.Contains
        ((Name.Sampling.approximation queryRoot.value.name).sample leftIndex) := by
      exact query.refines.contains
        (CertifiedSquareRoot.Sampling.candidate_in_initial_box query.owner queryRoot_eq actualPossible)
    have distance := edge.cached.preparedOwner.track.initial.box.normSq_sub_le_diagonalSq commonInside preparedInside
    have productPossible := Process.Based.based_initial_persists targetChannel.name.process targetReading.state
      (Process.Sampling.witnessAt_possible targetBased.name.process targetBased.name.state rightIndex)
    have paid := CachedSource.sum_lower sourceLower sourceClose distance (targetMovement productPossible) payment
    rewrite [Norm.Basic.normSq_eq_canonical] at paid
    exact paid
  have square : SquareRootProvenance.SquareIdentity queryRoot.value (curve.polynomial.eval (edge.point time)) :=
    queryRoot.square
  let derived := SquareRootProvenance.equivalent_of_sum_lower square basedSquare floor positive sumLower
  have actualName : queryRoot.value.name = ownerRootName query.owner.parameterNonzero query.owner :=
    congrArg (fun root : CertifiedSquareRoot.Certificate (curve.polynomial.eval (edge.point time)) => root.value.name)
      queryRoot_eq
  exact NamedEquivalent.transport (query.name_eq.trans actualName.symm).symm rfl
    (derived.trans targetEquivalent.symm)

end Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge.Query
