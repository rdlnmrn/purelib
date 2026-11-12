module

import Purelib.Riemann.RootContinuation.CoherentRoot.Identification
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.RootContinuation.CoherentRoot.Assignment
import Purelib.Tactic.OperationalEquivalence
import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
import Purelib.Riemann.RootContinuation.CoherentRoot.PointSeparation
import Purelib.Riemann.RootContinuation.CoherentRoot.PairSeparation
import Purelib.Riemann.RootContinuation.CoherentRoot.FactorRegion
import Purelib.Riemann.RootContinuation.CoherentRoot.FactorRegion.Assignment
import Purelib.Riemann.RootContinuation.CoherentRoot.CommonSource
import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
import Purelib.Approximation.Gaussian.Division.Prepared.Quotient
import Purelib.Polynomial.Power.Gaussian.Squarefree
meta import Purelib.Polynomial.Power.Gaussian.Squarefree
meta import Purelib.Polynomial.Dense.Gaussian.Squarefree.Union
meta import Purelib.Polynomial.Dense.Gaussian.Roots.Linear
meta import Purelib.Polynomial.Dense.Gaussian.Linear.Translated.Squarefree
import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Comparison
import Purelib.RootIsolation.Exact.LargeSquare
import Purelib.Polynomial.Clearance.Box.Boundary.RootRadius
import Purelib.Polynomial.Winding.Box.Global
import Purelib.Geometry.Rational.Box.Basic

/-!
# Prepared original-root identification and cache reuse

The quantified clients retain independent original root caches and request
starts. A concrete degree-three input specializes the arbitrary-degree builder;
its original polynomial and isolation count are retained without a cubic type.
-/

namespace TestPurelib.Riemann.RootIdentification

open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation
open Purelib.Polynomial
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial.Dense.Gaussian.Linear
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Geometry.Rational (Box)

-- Preserve the complete original symmetric-square constructor, including its
-- region, extraction policy, ordered output and refinement functions.
example {polynomial : CoherentRoot.GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    {radius : Rational} (radiusLe : RootRadius.denseLargeSquareRadius polynomial ≤ radius) :
    Exact.LargeSquare.isolateSymmetric input.degreeAtLeastTwo input.squarefree input.elimination radiusLe = (by
      have positive := (RootRadius.denseLargeSquareRadius_pos polynomial).trans_le radiusLe
      let box := Box.symmetric radius positive.le
      have negative := Arithmetic.neg_lt_neg_direct positive
      change -radius < 0 at negative
      let initial : Clearance.Box.Region.ClearRegion polynomial box :=
        { box := box
          refinesAmbient := Box.refines_refl box
          proper := ⟨negative.trans positive, negative.trans positive⟩
          clearance := Clearance.Box.Boundary.RootRadius.symmetric_boundaryClearance input.degreePositive radiusLe }
      exact Exact.Build.isolateFromRegion input.degreeAtLeastTwo input.squarefree input.elimination initial
        polynomial.natDegree (Winding.Box.Global.quadrupledBoxWinding_symmetric_eq_degree
          input.degreePositive radiusLe) none) := rfl

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {head : CoherentRoot.WindingOneTrack polynomial ambient}
    {tail : List (CoherentRoot.WindingOneTrack polynomial ambient)}
    (root : CoherentRoot.CertifiedName head) (remaining : CoherentRoot.Family tail) :
    ((CoherentRoot.Family.cons root remaining).get 0).approximation = root.approximation := rfl

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {head : CoherentRoot.WindingOneTrack polynomial ambient}
    {tail : List (CoherentRoot.WindingOneTrack polynomial ambient)}
    (root : CoherentRoot.CertifiedName head) (remaining : CoherentRoot.Family tail)
    (index : Fin tail.length) :
    ((CoherentRoot.Family.cons root remaining).get index.succ).approximation =
      (remaining.get index).approximation := rfl

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box} {count : Nat}
    (input : FTA.Squarefree.Input polynomial)
    (output : Exact.Basic.Output polynomial ambient count) (cache : CoherentRoot.Family output.tracks)
    {track : CoherentRoot.WindingOneTrack polynomial ambient} (root : CoherentRoot.CertifiedName track)
    (selection : Exact.Ownership.Basic.OwnerSelection output track) :
    (CoherentRoot.Assignment.ofSelection input output cache root selection).selection.refined = selection.refined := rfl

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box} {count : Nat}
    {output : Exact.Basic.Output polynomial ambient count} {cache : CoherentRoot.Family output.tracks}
    {firstTrack secondTrack : CoherentRoot.WindingOneTrack polynomial ambient}
    {first : CoherentRoot.CertifiedName firstTrack} {second : CoherentRoot.CertifiedName secondTrack}
    (left : CoherentRoot.Assignment output cache first) (right : CoherentRoot.Assignment output cache second)
    (same : left.selection.owner = right.selection.owner)
    (firstStart secondStart : Nat) (target : Rational) (positive : 0 < target) :
    Equivalence.Comparison first.approximation second.approximation firstStart secondStart target :=
  (first.approximation_equivalent second (left.sameOwner right same)).compare firstStart secondStart target positive

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box} {count : Nat}
    {output : Exact.Basic.Output polynomial ambient count} {cache : CoherentRoot.Family output.tracks}
    {firstTrack secondTrack : CoherentRoot.WindingOneTrack polynomial ambient}
    {first : CoherentRoot.CertifiedName firstTrack} {second : CoherentRoot.CertifiedName secondTrack}
    (left : CoherentRoot.Assignment output cache first) (right : CoherentRoot.Assignment output cache second)
    (different : left.selection.owner ≠ right.selection.owner)
    (equivalent : Equivalence.NamedEquivalent first.value.name second.value.name) : False :=
  (left.distinguish right different).rejects equivalent

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box} {count : Nat}
    {output : Exact.Basic.Output polynomial ambient count} {cache : CoherentRoot.Family output.tracks}
    {firstTrack secondTrack : CoherentRoot.WindingOneTrack polynomial ambient}
    {first : CoherentRoot.CertifiedName firstTrack} {second : CoherentRoot.CertifiedName secondTrack}
    (left : CoherentRoot.Assignment output cache first) (right : CoherentRoot.Assignment output cache second)
    (same : left.selection.owner = right.selection.owner)
    (leftCursor rightCursor : Name.Coherent.CCL.Cursor.Basic.ChannelCursor)
    (leftEq : leftCursor.channel = first.value) (rightEq : rightCursor.channel = second.value)
    (leftRequests rightRequests : List Name.Coherent.CCL.Cursor.Basic.ChannelCursor.RequestStep) :
    Name.Coherent.CCL.Cursor.Basic.ChannelCursor.ScheduleComparison
      leftCursor rightCursor leftRequests rightRequests := by
  have equivalent := left.sameOwner right same
  rewrite [← leftEq, ← rightEq] at equivalent
  exact Name.Coherent.CCL.Cursor.Basic.ChannelCursor.compareSchedules leftCursor rightCursor
    (Law.Basic.BitLaw.ofEquivalent equivalent) leftRequests rightRequests

/-- The original coefficient table of the concrete degree-three admission client. -/
def cubicPolynomial : CoherentRoot.GaussianPolynomial := Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩

/-- Executable squarefree admission uses the existing degree-generic power-polynomial certificate. -/
def cubicInput : FTA.Squarefree.Input cubicPolynomial where
  squarefree := Power.Gaussian.Squarefree.squarefree (by decide : (2 : CoherentRoot.Gaussian) ≠ 0) ⟨3, by decide⟩
  degreeAtLeastTwo := by
    unfold cubicPolynomial
    rewrite [Power.Gaussian.rootPolynomial_degree]
    decide

/-- The concrete cubic reuses coefficient-first isolation and the general cached-family builder. -/
def cubicPartition : CoherentRoot.Partition cubicInput := CoherentRoot.Partition.ofInput cubicInput

/-- Read an original cubic root at its original degree-bounded index without asserting a real-sheet choice. -/
def cubicRoot (index : Fin cubicPolynomial.natDegree) :
    CoherentRoot.CertifiedName (cubicPartition.output.trackAt index) :=
  cubicPartition.roots.get (cubicPartition.output.trackIndex index)

example (index : Fin cubicPolynomial.natDegree) :
    Equivalence.NamedEquivalent
      (Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner.polynomialEval
        cubicPolynomial (cubicRoot index).value).name
      (CoherentNamed.Coherence.exact 0).name :=
  (cubicRoot index).polynomial_zero

example (first second : Fin cubicPolynomial.natDegree) :
    CoherentRoot.ComparisonResult cubicPartition.output cubicPartition.roots (cubicRoot first) (cubicRoot second) :=
  cubicPartition.compare (cubicRoot first) (cubicRoot second)

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box} {count : Nat}
    {output : Exact.Basic.Output polynomial ambient count} {cache : CoherentRoot.Family output.tracks}
    {firstTrack secondTrack : CoherentRoot.WindingOneTrack polynomial ambient}
    {first : CoherentRoot.CertifiedName firstTrack} {second : CoherentRoot.CertifiedName secondTrack}
    (left : CoherentRoot.Assignment output cache first) (right : CoherentRoot.Assignment output cache second)
    (same : left.selection.owner = right.selection.owner) :
    Equivalence.NamedEquivalent
      (CoherentNamed.mul first.value (CoherentNamed.add first.value (CoherentNamed.Coherence.exact 1))).name
      (CoherentNamed.add (CoherentNamed.mul second.value second.value) second.value).name := by
  ccl_equiv [left.sameOwner right same]

/-- The original cubic evaluates to the retained nonzero exact value minus three at minus one. -/
theorem cubic_at_minus_one : cubicPolynomial.eval (-1) = -3 := by
  unfold cubicPolynomial
  exact (Power.Gaussian.rootPolynomial_eval 2 (-1) ⟨3, by decide⟩).trans (by decide +kernel)

/-- Compute each original cubic root's own stage and positive gap from minus one, with no supplied gap or budget. -/
def cubicPointGap (index : Fin cubicPolynomial.natDegree) (start : Nat) :
    CoherentRoot.PointSeparation (cubicRoot index) (-1) start :=
  CoherentRoot.PointSeparation.ofValue (cubicRoot index) (-1) (-3) cubic_at_minus_one (by decide +kernel) start

/-- Prepare the original one-plus-cubic-root channel from its coefficient-computed gap, preserving summand order. -/
def cubicDenominator (index : Fin cubicPolynomial.natDegree) (start : Nat) :
    Division.Prepared (CoherentNamed.add (CoherentNamed.Coherence.exact 1) (cubicRoot index).value) := by
  have prepared := (cubicPointGap index start).prepareDifference
  change Division.Prepared (CoherentNamed.add (cubicRoot index).value (CoherentNamed.Coherence.exact 1)) at prepared
  exact prepared.transport (by ccl_equiv)

/-- Retain ordinary division by the original one-plus-root expression and its actual computed preparation. -/
def cubicReciprocal (index : Fin cubicPolynomial.natDegree) (start : Nat) :
    Division.Prepared.Quotient (CoherentNamed.Coherence.exact 1)
      (CoherentNamed.add (CoherentNamed.Coherence.exact 1) (cubicRoot index).value) :=
  Division.Prepared.Quotient.quotient (CoherentNamed.Coherence.exact 1) (cubicDenominator index start)

/-- Every original cubic sheet supplies the original-channel equation through the degree-generic root API. -/
def cubicPowerIdentity (index : Fin cubicPolynomial.natDegree) :
    Provenance.Power.PowerIdentity (cubicRoot index).value 3 2 :=
  (cubicRoot index).power_identity

example (index : Fin cubicPolynomial.natDegree) :
    Equivalence.NamedEquivalent
      (CoherentNamed.mul (CoherentNamed.add (CoherentNamed.Coherence.exact 1) (cubicRoot index).value)
        (CoherentNamed.add
          (CoherentNamed.add (Name.Coherent.Power.namedPower (cubicRoot index).value 2)
            (CoherentNamed.neg (cubicRoot index).value))
          (CoherentNamed.Coherence.exact 1))).name
      (CoherentNamed.Coherence.exact 3).name := by
  ccl_equiv [cubicPowerIdentity index]

/-- An independently represented degree-three polynomial with a different retained exact parameter. -/
def neighboringPolynomial : CoherentRoot.GaussianPolynomial := Power.Gaussian.rootPolynomial 3 ⟨3, by decide⟩

/-- The second original coefficient table supplies its own degree-generic squarefree admission. -/
def neighboringInput : FTA.Squarefree.Input neighboringPolynomial where
  squarefree := Power.Gaussian.Squarefree.squarefree (by decide : (3 : CoherentRoot.Gaussian) ≠ 0) ⟨3, by decide⟩
  degreeAtLeastTwo := by
    unfold neighboringPolynomial
    rewrite [Power.Gaussian.rootPolynomial_degree]
    decide

/-- Retain the independent second polynomial's original coefficient-first partition and root cache. -/
def neighboringPartition : CoherentRoot.Partition neighboringInput := CoherentRoot.Partition.ofInput neighboringInput

/-- Read one independently cached second-polynomial root at its original bounded index. -/
def neighboringRoot (index : Fin neighboringPolynomial.natDegree) :
    CoherentRoot.CertifiedName (neighboringPartition.output.trackAt index) :=
  neighboringPartition.roots.get (neighboringPartition.output.trackIndex index)

/-- Kernel-check the constant completed Euclidean gcd of the two original degree-three coefficient tables. -/
def neighboringCoprime : Dense.Gaussian.Coprime.Basic.CoprimeCertificate cubicPolynomial neighboringPolynomial :=
  let result := Dense.Gaussian.GCD.extendedGCD cubicPolynomial neighboringPolynomial
  Dense.Gaussian.Coprime.Decision.certificateOfConstantGCD cubicPolynomial neighboringPolynomial
    result rfl (result.nonzero (.inl (by decide +kernel))) (by decide +kernel)

/-- Compute the original pair's gap from its checked coefficients and each caller's original starting stage. -/
def neighboringGap (first : Fin cubicPolynomial.natDegree) (second : Fin neighboringPolynomial.natDegree)
    (firstStart secondStart : Nat) :
    CoherentRoot.PairSeparation (cubicRoot first) (neighboringRoot second) firstStart secondStart :=
  CoherentRoot.PairSeparation.ofCoprime (cubicRoot first) (neighboringRoot second)
    neighboringCoprime firstStart secondStart

/-- Prepare the original difference of two independently cached cubic channels with no supplied denominator bound. -/
def neighboringDenominator (first : Fin cubicPolynomial.natDegree) (second : Fin neighboringPolynomial.natDegree)
    (firstStart secondStart : Nat) :
    Division.Prepared (CoherentNamed.add (cubicRoot first).value (CoherentNamed.neg (neighboringRoot second).value)) :=
  (neighboringGap first second firstStart secondStart).prepareSubtraction

/-- The independent source polynomial retains the original cubic and its displayed linear cofactor. -/
def sourcePolynomial : CoherentRoot.GaussianPolynomial := cubicPolynomial * (⟨[1, 0]⟩ : CoherentRoot.GaussianPolynomial)

/-- The source polynomial's own completed derivative gcd supplies its squarefree admission. -/
def sourceInput : FTA.Squarefree.Input sourcePolynomial where
  squarefree :=
    let result := Dense.Gaussian.GCD.extendedGCD sourcePolynomial (Dense.Gaussian.GCD.derivative sourcePolynomial)
    Dense.Gaussian.Coprime.Decision.certificateOfConstantGCD sourcePolynomial
      (Dense.Gaussian.GCD.derivative sourcePolynomial) result rfl
      (result.nonzero (.inl (by decide +kernel))) (by decide +kernel)
  degreeAtLeastTwo := by decide +kernel

/-- Kernel-check coprimality of the original cubic and its nonzero linear source cofactor. -/
def sourceCoprime : Dense.Gaussian.Coprime.Basic.CoprimeCertificate cubicPolynomial ⟨[1, 0]⟩ :=
  let result := Dense.Gaussian.GCD.extendedGCD cubicPolynomial ⟨[1, 0]⟩
  Dense.Gaussian.Coprime.Decision.certificateOfConstantGCD cubicPolynomial ⟨[1, 0]⟩ result rfl
    (result.nonzero (.inl (by decide +kernel))) (by decide +kernel)

/-- Compute the protected original cubic stage and its winding-one region for the original quartic source. -/
def sourceRegion (index : Fin cubicPolynomial.natDegree) (start : Nat) :
    CoherentRoot.FactorRegion (cubicRoot index) sourcePolynomial ⟨[1, 0]⟩ start :=
  CoherentRoot.FactorRegion.ofRoot (cubicRoot index) sourcePolynomial ⟨[1, 0]⟩
    sourceInput.nonzero (by decide +kernel) sourceCoprime start

/-- Retain the quartic source's own finite extraction, root cache and comparison to the original cubic channel. -/
def sourceRealization (index : Fin cubicPolynomial.natDegree) (start : Nat) :
    CoherentRoot.FactorRegion.Realization (sourceRegion index start) :=
  (sourceRegion index start).realize sourceInput

example (index : Fin cubicPolynomial.natDegree) (start : Nat) :
    Equivalence.NamedEquivalent (sourceRealization index start).root.value.name (cubicRoot index).value.name :=
  (sourceRealization index start).equivalent

example (index : Fin cubicPolynomial.natDegree) (start : Nat) :
    Equivalence.NamedEquivalent
      (Name.Coherent.Power.namedPower (sourceRealization index start).root.value 3).name
      (CoherentNamed.Coherence.exact 2).name := by
  ccl_equiv [(sourceRealization index start).equivalent, cubicPowerIdentity index]

/-- Prepare one quartic source partition on a computed support containing the original cubic ambient. -/
def commonSourcePartition : CoherentRoot.Partition sourceInput
    (Dense.Gaussian.Bounds.RootRadius.Box.enclosingSquare sourcePolynomial
      [Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox cubicPolynomial]) :=
  CoherentRoot.Partition.ofBoxes sourceInput [Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox cubicPolynomial]

/-- Assign each original cubic channel to its retained quartic source owner with its computed ownership budget. -/
def sourceAssignment (index : Fin cubicPolynomial.natDegree) (start : Nat) :
    CoherentRoot.FactorRegion.Assignment (sourceRegion index start)
      commonSourcePartition.output commonSourcePartition.roots :=
  CoherentRoot.FactorRegion.Assignment.ofOutput (sourceRegion index start) sourceInput
    commonSourcePartition.output commonSourcePartition.roots (by
      rewrite [commonSourcePartition.support_eq]
      exact (cubicPartition.output.trackAt index).initial.refinesAmbient.trans
        (Dense.Gaussian.Bounds.RootRadius.Box.refines_enclosingSquare sourcePolynomial (List.Mem.head _)))

example (index : Fin cubicPolynomial.natDegree) (start : Nat) :
    Equivalence.NamedEquivalent (cubicRoot index).value.name
      (commonSourcePartition.roots.get (sourceAssignment index start).owner).value.name :=
  (sourceAssignment index start).equivalent sourceInput

example (index : Fin cubicPolynomial.natDegree) (start : Nat) :
    Equivalence.NamedEquivalent
      (Name.Coherent.Power.namedPower
        (commonSourcePartition.roots.get (sourceAssignment index start).owner).value 3).name
      (CoherentNamed.Coherence.exact 2).name := by
  ccl_equiv [(sourceAssignment index start).equivalent sourceInput, cubicPowerIdentity index]

/-- Compute the independent cubic/quartic comparison from their original coefficient inputs alone. -/
def cubicQuarticComparison (index : Fin cubicPolynomial.natDegree) (sourceStart factorStart : Nat) :
    CoherentRoot.CommonSource.PreparedComparison sourceInput.toPositive cubicInput.toPositive
      (sourceRealization index sourceStart).root (cubicRoot index) sourceStart factorStart :=
  CoherentRoot.CommonSource.prepareComparison sourceInput.toPositive cubicInput.toPositive
    (sourceRealization index sourceStart).root (cubicRoot index) sourceStart factorStart

/-- The computed decision agrees with the independently established original cubic/quartic comparison. -/
def cubicQuarticEquivalent (index : Fin cubicPolynomial.natDegree) (sourceStart factorStart : Nat) :
    Equivalence.NamedEquivalent (sourceRealization index sourceStart).root.value.name (cubicRoot index).value.name := by
  cases (cubicQuarticComparison index sourceStart factorStart).comparison with
  | equal equivalent => exact equivalent
  | distinct separation => exact (separation.rejects (sourceRealization index sourceStart).equivalent).elim

/-- Compare original roots of two coprime cubic polynomials without supplied separation evidence. -/
def independentCubicComparison (first : Fin cubicPolynomial.natDegree) (second : Fin neighboringPolynomial.natDegree)
    (firstStart secondStart : Nat) :
    CoherentRoot.CommonSource.PreparedComparison cubicInput.toPositive neighboringInput.toPositive
      (cubicRoot first) (neighboringRoot second) firstStart secondStart :=
  CoherentRoot.CommonSource.prepareComparison cubicInput.toPositive neighboringInput.toPositive
    (cubicRoot first) (neighboringRoot second) firstStart secondStart

/-- Read the computed cubic outcome as a positive original-sample gap, excluding its impossible equality branch. -/
def independentCubicSeparation (first : Fin cubicPolynomial.natDegree) (second : Fin neighboringPolynomial.natDegree)
    (firstStart secondStart : Nat) :
    CoherentRoot.PairSeparation (cubicRoot first) (neighboringRoot second) firstStart secondStart := by
  cases (independentCubicComparison first second firstStart secondStart).comparison with
  | equal equivalent => exact ((neighboringGap first second firstStart secondStart).rejects equivalent).elim
  | distinct separation => exact separation

example (first : Fin cubicPolynomial.natDegree) (second : Fin neighboringPolynomial.natDegree)
    (firstStart secondStart : Nat) :
    Division.Prepared (CoherentNamed.add (cubicRoot first).value (CoherentNamed.neg (neighboringRoot second).value)) :=
  (independentCubicSeparation first second firstStart secondStart).prepareSubtraction

/-- Execute finite union coefficients for shared and coprime inputs and check both original factor readbacks. -/
private meta def checkUnionCoefficients : IO Unit := do
  let first := Power.Gaussian.rootPolynomial 2 ⟨2, by decide +kernel⟩
  let second := Power.Gaussian.rootPolynomial 3 ⟨2, by decide +kernel⟩
  let firstSquarefree := Power.Gaussian.Squarefree.squarefree (by decide +kernel : (2 : CoherentRoot.Gaussian) ≠ 0)
    ⟨2, by decide +kernel⟩
  let secondSquarefree := Power.Gaussian.Squarefree.squarefree (by decide +kernel : (3 : CoherentRoot.Gaussian) ≠ 0)
    ⟨2, by decide +kernel⟩
  let shared := Dense.Gaussian.Squarefree.Union.ofInputs first first (by decide +kernel) (by decide +kernel)
    firstSquarefree firstSquarefree
  let coprime := Dense.Gaussian.Squarefree.Union.ofInputs first second (by decide +kernel) (by decide +kernel)
    firstSquarefree secondSquarefree
  unless shared.polynomial.natDegree = 2 ∧ coprime.polynomial.natDegree = 4 do
    throw (IO.userError "squarefree union duplicated a shared factor or discarded a coprime input")
  let point : CoherentRoot.Gaussian := 2
  unless coprime.polynomial.eval point = first.eval point * coprime.result.qFactor.eval point ∧
      coprime.polynomial.eval point = second.eval point * coprime.result.pFactor.eval point do
    throw (IO.userError "union execution discarded the retained ordered Euclidean complements")

#eval checkUnionCoefficients

/-- Execute linear union branches and the original leading-zero affine table's exact-root readback. -/
private meta def checkLinearCoefficients : IO Unit := do
  let zero := Translated.translatedCoordinate 0
  let one := Translated.translatedCoordinate 1
  let zeroSquarefree := Translated.Squarefree.certificate 0
  let oneSquarefree := Translated.Squarefree.certificate 1
  let shared := Dense.Gaussian.Squarefree.Union.ofInputs zero zero
    (Translated.Squarefree.translatedCoordinate_nonzero 0)
    (Translated.Squarefree.translatedCoordinate_nonzero 0) zeroSquarefree zeroSquarefree
  let different := Dense.Gaussian.Squarefree.Union.ofInputs zero one
    (Translated.Squarefree.translatedCoordinate_nonzero 0)
    (Translated.Squarefree.translatedCoordinate_nonzero 1) zeroSquarefree oneSquarefree
  unless shared.polynomial.natDegree = 1 ∧ different.polynomial.natDegree = 2 do
    throw (IO.userError "linear union did not distinguish its single common root from two distinct roots")
  let padded : CoherentRoot.GaussianPolynomial := ⟨[0, 2, -6]⟩
  let data := Dense.Gaussian.Roots.Linear.rootData (by decide +kernel : padded.natDegree = 1)
  unless data.point = 3 ∧ padded.eval 5 = data.leading * (5 - data.point) do
    throw (IO.userError "linear root data lost the original leading-zero polynomial readback")

#eval checkLinearCoefficients

section NearbyPayment

variable {polynomial : CoherentRoot.GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
  (output : Exact.Basic.Output polynomial (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox polynomial)
    polynomial.natDegree) (roots : CoherentRoot.Family output.tracks)
  (sample : CoherentRoot.Gaussian) {epsilon target : Rational} (positive : 0 < target)
  (small : epsilon ^ 2 < target / 128)
  (localized : Residual.Global.Assignment.AssignedResult input sample epsilon output)
  (paid : CoherentRoot.Refinement (roots.get localized.owner.owner) (max 0 1))
  (same : paid = CoherentRoot.Refinement.ofTarget (roots.get localized.owner.owner)
    (max 0 1) (((target / 4) / 4) / 4)
    (Field.div_pos_direct
      (Field.div_pos_direct
        (Field.div_pos_direct positive (by decide)) (by decide)) (by decide)))

example : CoherentRoot.Assignment.nearbyFromOwnerPaid input output roots sample positive small localized paid same =
    CoherentRoot.Assignment.nearby input output roots sample positive small localized :=
  CoherentRoot.Assignment.nearbyFromOwnerPaid_eq input output roots sample positive small localized paid same

example :
    (CoherentRoot.Assignment.nearbyFromOwnerPaid input output roots sample positive small localized paid same).owner =
      localized.owner.owner ∧
    (CoherentRoot.Assignment.nearbyFromOwnerPaid input output roots sample positive small localized paid same).index =
      paid.index :=
  ⟨CoherentRoot.Assignment.nearbyFromOwnerPaid_owner input output roots sample positive small localized paid same,
    CoherentRoot.Assignment.nearbyFromOwnerPaid_index input output roots sample positive small localized paid same⟩

example (later : Nat) (order : paid.index ≤ later) :
    Purelib.Data.Gaussian.Norm.Basic.normSq ((roots.get localized.owner.owner).approximation.sample later - sample) <
      target := by
  let nearby := CoherentRoot.Assignment.nearbyFromOwnerPaid input output roots sample positive small localized paid same
  have owner := CoherentRoot.Assignment.nearbyFromOwnerPaid_owner input output roots sample positive small
    localized paid same
  have index := CoherentRoot.Assignment.nearbyFromOwnerPaid_index input output roots sample positive small
    localized paid same
  have bound := nearby.close later (index.symm ▸ order)
  rewrite [owner] at bound
  exact bound

end NearbyPayment

end TestPurelib.Riemann.RootIdentification
