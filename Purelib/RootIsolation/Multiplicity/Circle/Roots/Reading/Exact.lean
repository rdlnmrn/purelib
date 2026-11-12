module

public import Purelib.RootIsolation.Multiplicity.Circle.Location
public import Purelib.Polynomial.Dense.Roots.Tower.Reading.Sampled
import Purelib.Polynomial.Dense.Roots.Tower.Reading.Realization.Roots
-- The exposed exact constructor retains the original singleton transport proof.
public import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Exact original linear roots at their same formal reading

One original exact Gaussian root pays its complete singleton source
schedule with zero residual. The same retained expansion and original
tower budget construct the endpoint; its formal root reads the original
point exactly, even for a parent reading with positive multiplication error.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.List.Membership (mem_singleton)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Roots.Certificate (ExactRoot)
open Purelib.Polynomial.Dense.Roots (Tower)
open Purelib.Polynomial.Dense.Roots.Tower (StageScalar Leading)
open Purelib.Polynomial.Dense.Roots.Tower.Reading (Parameters Budget Sources Sampled)
open Purelib.Polynomial.Dense.Roots.Tower.Reading
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.Algebra.Monogenic
open Purelib.Algebra.Monogenic.Cyclic.Element.Reading renaming Request → CyclicRequest
open Purelib.Algebra.Ring (Weight GaussianReading)

universe u

namespace Exact

section Current

variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
variable {adjunction : Companion.Adjunction polynomial}
variable {decreases : adjunction.division.quotient.natDegree + 1 = polynomial.natDegree}
variable {remaining : Tower (StageScalar adjunction) inferInstance inferInstance adjunction.division.quotient}
variable {parent : Weight K} {gain radius : Rational} {embed : Canonical → K} {coefficient : Canonical}
variable {parameters : Cyclic.Element.Reading.Parameters adjunction.table parent gain radius}
variable {reading : GaussianReading parent embed} {gain_eq : reading.gain = gain}

/-- A zero original observed residual makes the same actual child read its original generator exactly.

Only the original source-companion readback and exact embedded-scalar
action are used. The parent reading may have positive multiplication error.
-/
private theorem current_root (leading : Leading (.step adjunction decreases remaining) embed coefficient)
    (parameters : Cyclic.Element.Reading.Parameters adjunction.table parent gain radius)
    (reading : GaussianReading parent embed) (gain_eq : reading.gain = gain)
    (inverse : Canonical) (inverseEq : inverse = coefficient⁻¹) (inverseNorm : Rational)
    (inverseNormEq : inverseNorm = Norm.Basic.normSq inverse)
    (observed : DensePolynomial Canonical) (observedEq : observed = Map.map reading.read polynomial)
    (point : Canonical) (pointBound : Norm.Basic.normSq point ≤ radius)
    (remainder : Canonical) (remainderEq : remainder = observed.eval point)
    (zero : observed.eval point = 0) :
    (Sampled.sourceObservation leading parameters reading gain_eq inverse inverseEq inverseNorm inverseNormEq
      observed observedEq point pointBound remainder remainderEq).child.read adjunction.root = point := by
  let current := Sampled.sourceCompanion leading reading inverse inverseEq observed observedEq
  have currentEq : current.observed = observed := current.observed_eq.trans observedEq.symm
  have error := adjunction.root_reading_error current reading.mapZero point
  rewrite [currentEq, zero, zero_mul, neg_zero] at error
  have vanished : (if 1 = polynomial.natDegree then (0 : Canonical) else 0) = 0 := by
    by_cases degree : 1 = polynomial.natDegree
    · rewrite [if_pos degree]; rfl
    · rewrite [if_neg degree]; rfl
  rewrite [vanished] at error
  rewrite [Cyclic.Element.Reading.Observation.read_apply]
  change Cyclic.Element.evaluate reading.read point adjunction.root = point
  calc
    _ = (Cyclic.Element.evaluate reading.read point adjunction.root - point) + point := by ring0
    _ = point := by rewrite [error, zero_add]; rfl

variable {target tolerance : Rational}
variable {current : Cyclic.Element.Reading.Parameters adjunction.table parent gain radius}
variable {next : Parameters remaining (Cyclic.Element.weight adjunction.table parent) current.gain radius}

/-- The same first original root retains an exact sampled reading through the actual remaining tower.

The original observed source vanishes at this same sampled point. Exact
tail scalar readback preserves that child reading. The proof reduces one
retained application directly, without a whole-function equation for the
recursive sampled constructor.
-/
private theorem first_read (tail : Budget next target tolerance) (request : CyclicRequest current tolerance)
    (leading : Leading (.step adjunction decreases remaining) embed coefficient)
    (reading : GaussianReading parent embed) (gain_eq : reading.gain = gain)
    {separation cap : Rational} (sources : Sources (.step tail request) leading separation cap)
    (observed : DensePolynomial Canonical) (observedEq : observed = Map.map reading.read polynomial)
    (point : Canonical) (expansion : Interpolation.Expansion observed [point])
    (bounded : ∀ next ∈ [point], Norm.Basic.normSq next ≤ radius) (paid : expansion.Pays sources.targets)
    (zero : observed.eval point = 0) :
    (sources.realize reading gain_eq observed observedEq [point] expansion bounded paid).realization.finalReading.read
      (remaining.embed adjunction.root) = point := by
  let observation := Sampled.sourceObservation leading current reading gain_eq sources.coefficientInverse
    sources.coefficientInverse_eq sources.inverseNorm sources.inverseNorm_eq observed observedEq point
    (bounded point List.mem_cons_self) expansion.first.remainder expansion.first.remainder_eval
  have paidOriginal : expansion.Pays ((Budget.step tail request).targets sources.scale cap) :=
    sources.targets_eq ▸ paid
  have residualPaid : observation.residual ≤ request.tolerance :=
    sources.scaled_residual_le request.tolerance_positive.le paidOriginal.head
  let rest := Sampled.ofExpansion tail leading.next observation.child observation.gain_eq sources.coefficientInverse
    sources.coefficientInverse_eq sources.inverseNorm sources.inverseNorm_eq sources.scale cap
    sources.scale_mul_norm_le_one expansion.first.quotient
    (Sampled.sourceQuotient_eq leading observation observed observedEq expansion) [] expansion.next
    (fun next member => bounded next (List.mem_cons_of_mem point member)) paidOriginal.next
  change (Realization.step (decreases := decreases) tail request observation residualPaid
    rest.realization).finalReading.read (remaining.embed adjunction.root) = point
  calc
    _ = observation.child.read adjunction.root :=
      Realization.final_read_first_root tail request observation residualPaid rest.realization
    _ = point := current_root leading current reading gain_eq sources.coefficientInverse sources.coefficientInverse_eq
      sources.inverseNorm sources.inverseNorm_eq observed observedEq point (bounded point List.mem_cons_self)
      expansion.first.remainder expansion.first.remainder_eval zero

end Current
end Exact

variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
variable {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
variable {parent : Weight K} {gain radius target tolerance : Rational}
variable {parameters : Parameters tower parent gain radius} {observed : DensePolynomial Canonical}
variable {embed : Canonical → K}

set_option genInjectivity false in
/-- The same original exact linear root, source schedule, expansion and paid formal reading.

The Gaussian factor and formal source remain separate owners connected by
the original coefficient reading. The singleton expansion has zero residual
and pays the fixed schedule; its actual sampled endpoint is retained with
the complete constructor equation rather than replaced by an exact model.
-/
structure Exact (budget : Budget parameters target tolerance)
    (leading : Leading tower embed observed.leadingCoeff) (reading : GaussianReading parent embed)
    (gain_eq : reading.gain = gain) (root : ExactRoot observed) where
  /-- The same formal source has its original degree one. -/
  sourceDegree : polynomial.natDegree = 1
  /-- The same original Gaussian factor has degree one. -/
  observedDegree : observed.natDegree = 1
  /-- The Gaussian factor reads the same original formal source coefficient table. -/
  observed_eq : observed = Map.map reading.read polynomial
  /-- The retained exact point quadrance, fixed before the model is assembled. -/
  pointNorm : Rational
  /-- The cache is the quadrance of the same original exact root. -/
  pointNorm_eq : pointNorm = Norm.Basic.normSq root.point
  /-- The original exact singleton stays within the fixed parameter radius. -/
  bounded : ∀ point ∈ [root.point], Norm.Basic.normSq point ≤ radius
  /-- The same original source targets, with unit separation and residual cap. -/
  sources : Sources budget leading 1 1
  /-- The source request is its complete original constructor result. -/
  sources_eq : sources = Sources.prepare budget leading 1 1 (by decide +kernel) (by decide +kernel)
  /-- One actual original synthetic expansion of that same exact singleton. -/
  expansion : Interpolation.Expansion observed [root.point]
  /-- The retained expansion is the same original source procedure. -/
  expansion_eq : expansion = Interpolation.Expansion.prepare observed [root.point]
  /-- The actual retained division pays every original scheduled source target. -/
  payment : expansion.Pays sources.targets
  /-- The actual original sampled endpoint and all its paid observations. -/
  sampled : Sampled budget reading gain_eq [root.point] (1 * sources.inverseNorm)
  /-- The model is constructed from those same cached source requests and expansion. -/
  sampled_eq : sampled = sources.realize reading gain_eq observed observed_eq [root.point] expansion bounded payment

constructive_injectivity Exact

namespace Exact

variable (budget : Budget parameters target tolerance) (leading : Leading tower embed observed.leadingCoeff)
variable (reading : GaussianReading parent embed) (gain_eq : reading.gain = gain) (root : ExactRoot observed)

/-- Assemble the exact branch from the same already retained root quadrance and original source owners.

The exact zero source residual pays the complete original sufficient
schedule. Only one original source request, one singleton expansion and
one actual sampled reading are computed; no isolation or formal root
construction occurs here.
-/
@[expose] def ofNorm (sourceDegree : polynomial.natDegree = 1) (observedDegree : observed.natDegree = 1)
    (observedEq : observed = Map.map reading.read polynomial)
    (pointNorm : Rational) (pointNormEq : pointNorm = Norm.Basic.normSq root.point)
    (pointBound : Norm.Basic.normSq root.point ≤ radius) : Exact budget leading reading gain_eq root :=
  let sources := Sources.prepare budget leading 1 1 (by decide +kernel) (by decide +kernel)
  let expansion := Interpolation.Expansion.prepare observed [root.point]
  have bounded : ∀ point ∈ [root.point], Norm.Basic.normSq point ≤ radius :=
    fun _ member => (mem_singleton.mp member).symm ▸ pointBound
  have atRoot : Norm.Basic.normSq (observed.eval root.point) ≤ sources.schedule.val.initial := by
    rewrite [root.root, Norm.Basic.normSq_zero]
    exact sources.initial_positive.le
  have samples : ∀ point ∈ [root.point], Norm.Basic.normSq (observed.eval point) ≤ sources.schedule.val.initial :=
    fun _ member => (mem_singleton.mp member).symm ▸ atRoot
  have separated : [root.point].Pairwise (fun left right => (1 : Rational) ≤ Norm.Basic.normSq (left - right)) :=
    .cons (by intro point member; cases member) .nil
  have count : sources.targets.length = [root.point].length := sources.targets_length_eq_degree.trans sourceDegree
  have payment := expansion.pays sources.separationPositive sources.schedule.val sources.schedule.property
    count separated samples
  let sampled := sources.realize reading gain_eq observed observedEq [root.point] expansion bounded payment
  { sourceDegree, observedDegree, observed_eq := observedEq, pointNorm, pointNorm_eq := pointNormEq,
    bounded, sources, sources_eq := rfl, expansion, expansion_eq := rfl, payment, sampled, sampled_eq := rfl }

/-- Compute the original exact point quadrance once and assemble its same actual paid reading. -/
@[expose] def prepare (sourceDegree : polynomial.natDegree = 1) (observedDegree : observed.natDegree = 1)
    (observedEq : observed = Map.map reading.read polynomial)
    (pointBound : Norm.Basic.normSq root.point ≤ radius) : Exact budget leading reading gain_eq root :=
  let pointNorm := Norm.Basic.normSq root.point
  ofNorm budget leading reading gain_eq root sourceDegree observedDegree observedEq pointNorm rfl pointBound

variable {budget leading reading gain_eq root}

/-- Retained original caches restore the complete same exact-branch constructor on the retained quadrance. -/
theorem restore (retained : Exact budget leading reading gain_eq root) :
    retained = ofNorm budget leading reading gain_eq root retained.sourceDegree retained.observedDegree
      retained.observed_eq retained.pointNorm retained.pointNorm_eq
        (retained.bounded root.point List.mem_cons_self) := by
  cases retained with
  | mk sourceDegree observedDegree observedEq pointNorm pointNormEq bounded sources sourcesEq expansion expansionEq
      payment sampled sampledEq =>
      cases sourcesEq
      cases expansionEq
      cases sampledEq
      rfl

/-- Supplying the original exact point quadrance restores the complete convenience constructor. -/
theorem ofNorm_eq_prepare (sourceDegree : polynomial.natDegree = 1) (observedDegree : observed.natDegree = 1)
    (observedEq : observed = Map.map reading.read polynomial)
    (pointNorm : Rational) (pointNormEq : pointNorm = Norm.Basic.normSq root.point)
    (pointBound : Norm.Basic.normSq root.point ≤ radius) :
    ofNorm budget leading reading gain_eq root sourceDegree observedDegree observedEq pointNorm pointNormEq pointBound =
      prepare budget leading reading gain_eq root sourceDegree observedDegree observedEq pointBound := by
  cases pointNormEq
  rfl

/-- Every same original bounded tower root reads exactly the original exact Gaussian root point.

The endpoint preserves the actual first observation through its original
tail embeddings. The original observed zero residual removes even the
terminal correction, without a multiplicativity or zero-error assumption
on the parent reading.
-/
theorem read_root (retained : Exact budget leading reading gain_eq root) (index : Fin tower.blocks.length) :
    retained.sampled.realization.finalReading.read (tower.blocks[index.val]'index.isLt).point = root.point := by
  rewrite [retained.sampled_eq]
  cases tower with
  | constant => exact Fin.elim0 index
  | step adjunction decreases remaining =>
      cases parameters with
      | step current next =>
          cases budget with
          | step tail request =>
              have first := first_read tail request leading reading gain_eq retained.sources observed
                retained.observed_eq root.point retained.expansion retained.bounded retained.payment root.root
              have count := (Tower.blocks_length (.step adjunction decreases remaining)).trans retained.sourceDegree
              rcases index with ⟨position, bound⟩
              cases position with
              | zero => exact first
              | succ position =>
                  have impossible : position + 1 < 1 := count ▸ bound
                  exact False.elim (Nat.not_lt_zero position (Nat.lt_of_succ_lt_succ impossible))

/-- The same original formal-root reading has the cached exact-point quadrance. -/
theorem normSq_root (retained : Exact budget leading reading gain_eq root) (index : Fin tower.blocks.length) :
    Norm.Basic.normSq (retained.sampled.realization.finalReading.read (tower.blocks[index.val]'index.isLt).point) =
      retained.pointNorm :=
  (congrArg Norm.Basic.normSq (retained.read_root index)).trans retained.pointNorm_eq.symm

/-- The retained exact point quadrance is nonnegative. -/
theorem pointNorm_nonnegative (retained : Exact budget leading reading gain_eq root) : 0 ≤ retained.pointNorm := by
  rewrite [retained.pointNorm_eq]
  exact Norm.Basic.normSq_nonneg root.point

/-- The original strict exact-root location supplies the same formal reading's fixed ceiling or floor.

The source-fixed point quadrance is a nonnegative ceiling strictly below
one in the inside branch and a floor strictly above one in the outside
branch. Both comparisons follow the proved exact endpoint equality.
-/
theorem radial (retained : Exact budget leading reading gain_eq root) {clearance : Certificate observed}
    (location : ExactLocation clearance root) (index : Fin tower.blocks.length) :
    match location with
    | .inside _ => retained.pointNorm < 1 ∧
        Norm.Basic.normSq (retained.sampled.realization.finalReading.read
          (tower.blocks[index.val]'index.isLt).point) ≤ retained.pointNorm
    | .outside _ => 1 < retained.pointNorm ∧ retained.pointNorm ≤
        Norm.Basic.normSq (retained.sampled.realization.finalReading.read
          (tower.blocks[index.val]'index.isLt).point) := by
  have original : retained.pointNorm = root.point.normSq :=
    retained.pointNorm_eq.trans (Norm.Basic.normSq_eq_canonical root.point)
  cases location with
  | inside holds => exact ⟨original.symm ▸ holds, (retained.normSq_root index).le⟩
  | outside holds => exact ⟨original.symm ▸ holds, (retained.normSq_root index).symm.le⟩

end Exact

end Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading

end
