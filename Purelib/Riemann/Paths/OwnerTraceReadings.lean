module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Branches.SquareRootSheets
import Purelib.Riemann.Topology.SquareRootContinuationChain

public import Purelib.Riemann.RootContinuation.SquareRootTrace
public import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Polynomial.Dense.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Interval.Basic
import Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.CoherentRoot
public import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Data.Nat.Order
import Purelib.RootIsolation.State.WindingOne.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Actual owner readings and stationary trace handoffs

A residual request selects a finite state of the supplied division-ready root
name.  Every later displayed reading has the same positive root margin and
the requested residual.  Operational equivalence synchronizes two such tails
closely enough to certify a stationary square-root trace edge, including after
arbitrary further index refinement.  This supplies the joins needed when
preparation or recentering changes an owner's presentation, not its root.
-/

namespace Purelib.Riemann.Paths.OwnerTraceReadings

open Purelib.Data.Rat.Fraction.Order

open Purelib.Riemann.RootContinuation.SquareRootTrace
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense

/-- The original winding-one quadratic root owner indexed by its exact parameter. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat in
/-- Division by the positive rational 1024 preserves the original weak inequality. -/
private theorem div_1024_mono {left right : Fraction.Rational} (bound : left ≤ right) :
    left / 1024 ≤ right / 1024 := by
  apply (Fraction.Order.Field.div_le_iff_pos
    (by decide +kernel : (0 : Fraction.Rational) < 1024)).mpr
  rw [Fraction.Field.div_mul_cancel_of_ne _ _
    (by decide +kernel : (1024 : Fraction.Rational) ≠ 0)]
  exact bound

open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- The original executable approximation sequence of the retained root owner's track. -/
abbrev ownerApproximation {parameter : Basic.Canonical} (owner : Owner parameter) :=
  CertifiedSquareRoot.approximation owner.track

open Purelib.Data.Gaussian in
/-- The original apart Gaussian root name carried by the retained owner certificate. -/
abbrev ownerName {parameter : Basic.Canonical} (owner : Owner parameter) :=
  (owner.certificate owner.parameterNonzero).value.name

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- A retained approximation tail with a positive sample-norm lower bound and uniform quadratic residual bound.

The exact apart state supplies the starting index, and the residual target is the retained lower bound squared divided
by 1024, for the original parameter and approximation sequence. -/
structure ApproximationTail (parameter : Basic.Canonical)
    (approximation : Sequence.ApproximationData)
    (apart : Process.Apart.Possible.PossibleApart approximation.toProcess) where
  /-- The retained positive lower bound on all original approximation sample squared norms. -/ lower : Fraction.Rational
  /-- The retained sample-norm lower bound is strictly positive. -/ lower_positive : 0 < lower
  /-- Every original approximation sample satisfies that same retained lower bound. -/ lower_bound : ∀ index : Nat,
    lower ≤ normSq (approximation.sample index)
  /-- The retained quadratic residual request for the original approximation tail. -/ residualTarget : Fraction.Rational
  /-- The target equals the retained lower bound squared divided by 1024. -/ residualTarget_eq : residualTarget = lower
    ^ 2 / 1024
  /-- The original apart approximation state satisfying the retained residual request. -/ state :
    Process.Apart.Preparation.ApartState approximation.toProcess apart
  /-- The retained starting index of the original residual-certified tail. -/ first : Nat
  /-- The tail starts at exactly the retained apart state's source index. -/ first_eq : first = state.source
  /-- Every value possible at the original retained state satisfies the cached quadratic residual target. -/ residual :
    ∀ {value : Basic.Canonical}, approximation.Possible state.source value →
    normSq (value ^ 2 - parameter) ≤ residualTarget

constructive_injectivity ApproximationTail

open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- The original root owner's approximation tail with its exact retained apartness certificate. -/
abbrev OwnerTail {parameter : Basic.Canonical} (owner : Owner parameter) :=
  ApproximationTail parameter (ownerApproximation owner)
    (CertifiedSquareRoot.possibleApart owner.parameterNonzero owner.track)

namespace OwnerTail

variable {parameter : Purelib.Data.Gaussian.Basic.Canonical} {owner : Owner parameter}

open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Acquire an original owner's residual-certified tail at the squared sample-norm lower bound divided by 1024.

The retained residual state, exact source index and pointwise sample lower bound belong to that same original track and
nonzero parameter. -/
def acquire (owner : Owner parameter) : OwnerTail owner :=
  let lower := SquareRootSheets.sampleNormLower parameter
  have positive : 0 < lower := SquareRootSheets.sampleLower_positive owner.parameterNonzero
  let target : Fraction.Rational := lower ^ 2 / 1024
  have targetPositive : 0 < target := Fraction.Order.Field.div_pos_direct
    (Arithmetic.pow_pos_direct positive 2) (by decide +kernel)
  let state := CertifiedSquareRoot.residualState owner.parameterNonzero owner.track target targetPositive
  { lower := lower
    lower_positive := positive
    lower_bound := CertifiedSquareRoot.sample_norm_lower owner.parameterNonzero owner.track
    residualTarget := target
    residualTarget_eq := rfl
    state := state
    first := state.source
    first_eq := rfl
    residual := by
      intro value possible
      have bound := CertifiedSquareRoot.residualState_candidate_residual_lt
        owner.parameterNonzero owner.track target targetPositive possible
      simpa only [pow_two] using bound.le }

/-- The two actual acquired tails at one radicand retain the SAME intrinsic sample-norm lower bound.

The owners, tracks and apart states remain separate; this is only the
scalar lower-cache readback of the original acquisition algorithm.
-/
theorem acquire_lower_eq (left right : Owner parameter) :
    (acquire left).lower = (acquire right).lower := rfl

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- A cached reading of the original owner approximation at a retained index beyond the certified tail start.

The exact sample value, squared norm and squared quadratic residual are cached with equations, preserving the original
tail and index witness. -/
structure Reading (tail : OwnerTail owner) where
  /-- The retained original approximation reading index. -/ index : Nat
  /-- The reading index is no earlier than the original certified tail start. -/ later : tail.first ≤ index
  /-- The cached original approximation sample at the retained index. -/ value : Basic.Canonical
  /-- The cached value equals that exact original indexed sample. -/ value_eq : value = (ownerApproximation
    owner).sample index
  /-- The cached squared norm of the retained reading. -/ norm : Fraction.Rational
  /-- The norm cache equals the exact retained value's squared norm. -/ norm_eq : norm = normSq value
  /-- The cached squared quadratic residual of the retained reading. -/ residualNorm : Fraction.Rational
  /-- The residual cache equals the exact retained value squared minus the original parameter, in squared norm. -/
    residualNorm_eq : residualNorm = normSq (value ^ 2 - parameter)

constructive_injectivity Reading

namespace Reading

variable {tail : OwnerTail owner}

/-- Cache the original approximation sample, squared norm and quadratic residual at the supplied retained index beyond
the tail start. -/
def acquire (tail : OwnerTail owner) (index : Nat) (later : tail.first ≤ index) : Reading tail :=
  let value := (ownerApproximation owner).sample index
  { index := index
    later := later
    value := value
    value_eq := rfl
    norm := normSq value
    norm_eq := rfl
    residualNorm := normSq (value ^ 2 - parameter)
    residualNorm_eq := rfl }

/-- The retained reading is possible at the original tail's apart root state. -/
theorem possible (reading : Reading tail) :
    (ownerName owner).process.Possible tail.state reading.value := by
  change (ownerApproximation owner).Possible tail.state.source reading.value
  refine ⟨reading.index, ?_, reading.value_eq⟩
  rw [← tail.first_eq]
  exact reading.later

/-- The retained reading's cached squared norm satisfies the original tail lower bound. -/
theorem lower (reading : Reading tail) : tail.lower ≤ reading.norm := by
  rw [reading.norm_eq, reading.value_eq]
  exact tail.lower_bound reading.index

open Purelib.Data.Rat in
/-- The retained reading's cached residual is no larger than its squared norm squared divided by 1024. -/
theorem residual_small (reading : Reading tail) : reading.residualNorm ≤ reading.norm ^ 2 / 1024 := by
  rw [reading.residualNorm_eq]
  calc
    _ ≤ tail.residualTarget := tail.residual reading.possible
    _ = tail.lower ^ 2 / 1024 := tail.residualTarget_eq
    _ ≤ _ := div_1024_mono
      (Arithmetic.pow_le_pow_direct tail.lower_positive.le reading.lower 2)

end Reading

end OwnerTail

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- Two original approximation tails and their retained operational comparison at the left norm-relative target.

The comparison starts beyond both exact tail indices and keeps the two original sequences, apartness witnesses and
cached lower bounds separate. -/
structure ApproximationJoin (parameter : Basic.Canonical)
    (left right : Sequence.ApproximationData)
    (leftApart : Process.Apart.Possible.PossibleApart left.toProcess)
    (rightApart : Process.Apart.Possible.PossibleApart right.toProcess) where
  /-- The retained residual-certified tail of the exact original left approximation. -/ leftTail : ApproximationTail
    parameter left leftApart
  /-- The retained residual-certified tail of the exact original right approximation. -/ rightTail : ApproximationTail
    parameter right rightApart
  /-- The original two-tail comparison beyond both starting indices at the retained left lower bound divided by 1024. -/
    comparison : Equivalence.Comparison
    left right leftTail.first rightTail.first (leftTail.lower / 1024)

constructive_injectivity ApproximationJoin

open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- The original two root owners' retained approximation tails and comparison at their exact shared parameter. -/
abbrev OwnerJoin {parameter : Basic.Canonical} (left right : Owner parameter) :=
  ApproximationJoin parameter (ownerApproximation left) (ownerApproximation right)
    (CertifiedSquareRoot.possibleApart left.parameterNonzero left.track)
    (CertifiedSquareRoot.possibleApart right.parameterNonzero right.track)

namespace OwnerJoin

variable {parameter : Purelib.Data.Gaussian.Basic.Canonical} {left right : Owner parameter}

open Purelib.Approximation.Gaussian in
open Purelib.Data.Rat in
/-- Compare the two retained approximation tails at the exact left lower bound divided by 1024. -/
def ofApproximationTails (leftTail : OwnerTail left) (rightTail : OwnerTail right)
    (equivalent : Equivalence.Equivalent
      (ownerApproximation left) (ownerApproximation right)) : OwnerJoin left right :=
  { leftTail := leftTail
    rightTail := rightTail
    comparison := equivalent.compare leftTail.first rightTail.first (leftTail.lower / 1024)
      (Fraction.Order.Field.div_pos_direct leftTail.lower_positive (by decide +kernel)) }

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- Build a retained join from the original tails and operational equivalence of the two owner names. -/
def ofTails (leftTail : OwnerTail left) (rightTail : OwnerTail right)
    (equivalent : Equivalence.NamedEquivalent (ownerName left) (ownerName right)) :
    OwnerJoin left right :=
  let raw := SquareRootTrackEquivalence.approximationEquivalent_of_rootEquivalent
    left.parameterNonzero left.track right.track equivalent
  ofApproximationTails leftTail rightTail raw

open Purelib.Approximation.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
/-- Construct approximation equivalence from refinement of the original inner root-owner box to the outer box.

An already strict refinement uses the original tracks directly; otherwise an exact positive inner refinement supplies a
common strict tail while retaining both input approximations. -/
def approximationEquivalentOfRefines (outer inner : Owner parameter)
    (refines : inner.track.initial.box.Refines outer.track.initial.box) :
    Equivalence.Equivalent (ownerApproximation outer) (ownerApproximation inner) := by
  by_cases strict : inner.track.initial.box.StrictInterior outer.track.initial.box
  · exact SquareRootTrackEquivalence.approximationEquivalent_of_initial_strict
      outer.parameterNonzero outer.track inner.track strict
  · let common := inner.refineAt 1
    have commonStrict : common.track.initial.box.StrictInterior inner.track.initial.box :=
      SquareRootTrackEquivalence.state_strict_initial_of_pos inner.track (by decide)
    let outerToCommon := SquareRootTrackEquivalence.approximationEquivalent_of_initial_strict
      outer.parameterNonzero outer.track common.track
          ((Geometry.Rational.Box.Refinement.StrictInterior.Boxes.trans_refines
        commonStrict) refines)
    let innerToCommon := SquareRootTrackEquivalence.approximationEquivalent_of_initial_strict
      inner.parameterNonzero inner.track common.track commonStrict
    exact Equivalence.Equivalent.trans outerToCommon innerToCommon.symm

open Purelib.Approximation.Gaussian in
open Purelib.Geometry.Rational in
/-- Acquire both original residual-certified tails and construct their retained join.

The exact box-refinement decisions select a direct approximation comparison when available; otherwise the supplied
original name equivalence provides it. Both owner identities and tail indices remain unchanged. -/
def acquire (left right : Owner parameter)
    (equivalent : Equivalence.NamedEquivalent (ownerName left) (ownerName right)) :
    OwnerJoin left right := by
  let leftTail := OwnerTail.acquire left
  let rightTail := OwnerTail.acquire right
  letI : Decidable (right.track.initial.box.Refines left.track.initial.box) := by
    unfold Box.Refines
    infer_instance
  letI : Decidable (left.track.initial.box.Refines right.track.initial.box) := by
    unfold Box.Refines
    infer_instance
  by_cases rightRefines : right.track.initial.box.Refines left.track.initial.box
  · exact ofApproximationTails leftTail rightTail (approximationEquivalentOfRefines left right rightRefines)
  · by_cases leftRefines : left.track.initial.box.Refines right.track.initial.box
    · exact ofApproximationTails leftTail rightTail (approximationEquivalentOfRefines right left leftRefines).symm
    · exact ofTails leftTail rightTail equivalent

open Purelib.Approximation.Gaussian in
/-- Construct a reflexive owner join that reuses the same acquired original tail on both sides. -/
def reflexive (owner : Owner parameter) : OwnerJoin owner owner :=
  let tail := OwnerTail.acquire owner
  ofApproximationTails tail tail (Equivalence.Equivalent.refl _)

/-- Cache the original left-tail sample at the exact index retained by the join comparison. -/
def leftReading (join : OwnerJoin left right) : OwnerTail.Reading join.leftTail :=
  .acquire join.leftTail join.comparison.leftIndex join.comparison.left_ge

/-- Cache the original right-tail sample at the exact index retained by the join comparison. -/
def rightReading (join : OwnerJoin left right) : OwnerTail.Reading join.rightTail :=
  .acquire join.rightTail join.comparison.rightIndex join.comparison.right_ge

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Every later original left sample stays within one 256th of the same retained left reading's squared norm.

The actual join comparison bounds both samples through its one retained
right-side index. The original left reading and both tail caches remain
unchanged, and the sharper constant is already paid by that comparison.
-/
theorem sample_near_leftReading (join : OwnerJoin left right) (index : Nat)
    (later : join.comparison.leftIndex ≤ index) :
    normSq ((ownerApproximation left).sample index - join.leftReading.value) ≤ join.leftReading.norm / 256 := by
  let reference := join.leftReading
  have firstClose := join.comparison.close later (Nat.le_refl join.comparison.rightIndex)
  have referenceClose := join.comparison.close
    (Nat.le_refl join.comparison.leftIndex) (Nat.le_refl join.comparison.rightIndex)
  change Norm.Basic.normSq ((ownerApproximation left).sample reference.index -
    (ownerApproximation right).sample join.comparison.rightIndex) < _ at referenceClose
  rewrite [← reference.value_eq, Norm.Basic.normSq_eq_canonical] at referenceClose
  rewrite [Norm.Basic.normSq_eq_canonical] at firstClose
  have reverse : normSq ((ownerApproximation right).sample join.comparison.rightIndex -
      reference.value) = normSq (reference.value -
        (ownerApproximation right).sample join.comparison.rightIndex) := by
    rewrite [show (ownerApproximation right).sample join.comparison.rightIndex - reference.value =
      -(reference.value - (ownerApproximation right).sample join.comparison.rightIndex) by ring1,
      Basic.Canonical.normSq_neg]
    rfl
  have triangle := Norm.Bounds.normSq_sub_le_via
    ((ownerApproximation left).sample index)
    ((ownerApproximation right).sample join.comparison.rightIndex) reference.value
  simp only [Norm.Basic.normSq_eq_canonical] at triangle
  rewrite [reverse] at triangle
  calc
    _ ≤ 2 * (normSq ((ownerApproximation left).sample index -
        (ownerApproximation right).sample join.comparison.rightIndex) +
      normSq (reference.value - (ownerApproximation right).sample join.comparison.rightIndex)) :=
      triangle
    _ ≤ 2 * (join.leftTail.lower / 1024 + join.leftTail.lower / 1024) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct firstClose.le referenceClose.le) (by decide +kernel)
    _ ≤ 2 * (reference.norm / 1024 + reference.norm / 1024) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct
          (Fraction.Order.Field.divide_mono reference.lower (by decide +kernel))
          (Fraction.Order.Field.divide_mono reference.lower (by decide +kernel))) (by decide +kernel)
    _ = (4 * (1024 : Fraction.Rational)⁻¹) * reference.norm := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ = (256 : Fraction.Rational)⁻¹ * reference.norm :=
      congrArg (fun coefficient : Fraction.Rational => coefficient * reference.norm) (by decide +kernel)
    _ = reference.norm / 256 := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct]
      ring1

open Purelib.Data.Gaussian in
/-- Retained readings beyond both comparison indices satisfy the left-reading-relative squared distance bound. -/
theorem distance (join : OwnerJoin left right)
    (first : OwnerTail.Reading join.leftTail) (second : OwnerTail.Reading join.rightTail)
    (firstLater : join.comparison.leftIndex ≤ first.index)
    (secondLater : join.comparison.rightIndex ≤ second.index) :
    normSq (second.value - first.value) ≤ first.norm / 1024 := by
  have close := join.comparison.close firstLater secondLater
  rw [← first.value_eq, ← second.value_eq, Norm.Basic.normSq_eq_canonical] at close
  have reverse : normSq (second.value - first.value) = normSq (first.value - second.value) := by
    rw [← Basic.Canonical.normSq_neg (first.value - second.value)]
    congr 1
    ring1
  rw [reverse]
  exact close.le.trans (div_1024_mono first.lower)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Build a certified root trace edge between two retained joined readings at the same original base point.

The exact residual and distance certificates pay the edge smallness conditions; the retained base variation polynomial
is zero because the original base endpoints coincide. -/
def stationaryEdge (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (point :
  Basic.Canonical)
    {left right : Owner (polynomial.eval point)} (join : OwnerJoin left right)
    (first : OwnerTail.Reading join.leftTail) (second : OwnerTail.Reading join.rightTail)
    (firstLater : join.comparison.leftIndex ≤ first.index)
    (secondLater : join.comparison.rightIndex ≤ second.index) :
    Edge polynomial first.value second.value point point :=
  let data : EdgeData polynomial first.value second.value point point :=
    { rootNorm := first.norm
      rootNorm_eq := first.norm_eq
      distance := normSq (second.value - first.value)
      distance_eq := rfl
      residual := first.residualNorm
      residual_eq := first.residualNorm_eq
      variation := 0
      variation_eq := by
        intro time
        rw [Dense.Basic.DensePolynomial.eval_zero]
        have stationary : Affine.line point (point - point) time = point := by
          unfold Affine.line
          ring1
        rw [stationary, Basic.sub_self]
      movementBound := 0
      movementBound_valid := by
        intro time _inside
        rw [Dense.Basic.DensePolynomial.eval_zero, Basic.Canonical.normSq_zero] }
  { data := data
    checked := ⟨join.leftTail.lower_positive.trans_le first.lower,
      join.distance first second firstLater secondLater, first.residual_small,
      Fraction.Order.Field.div_nonneg_direct
        (Arithmetic.sq_nonneg_direct _) (by decide +kernel)⟩ }

section Equivalence

open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Nat
open Purelib.Riemann.RootContinuation

/-- Refine the same original joined approximation tails to any positive squared-distance request.

The retained join fixes the signed near branch, both original approximations
and their actual comparison floors. Each request pays two original residual
indices and uses the same positive left-tail lower bound in the shared
square-residual distance theorem. It does not rerun root isolation or either
source preparation.
-/
def approximationEquivalent (join : OwnerJoin left right) :
    Equivalence.Equivalent (ownerApproximation left) (ownerApproximation right) where
  compare := by
    intro leftStart rightStart target positive
    let residualTarget := target * join.leftTail.lower / 4
    have residualPositive : 0 < residualTarget := Fraction.Order.Field.div_pos_direct
      (Arithmetic.mul_pos_direct positive join.leftTail.lower_positive) (by decide +kernel)
    let leftResidual := CertifiedSquareRoot.residualIndex left.track residualTarget residualPositive
    let rightResidual := CertifiedSquareRoot.residualIndex right.track residualTarget residualPositive
    let leftFloor := max leftStart join.comparison.leftIndex
    let rightFloor := max rightStart join.comparison.rightIndex
    have leftStartBound : leftStart ≤ leftFloor := by
      dsimp only [leftFloor]
      rewrite [Order.max_eq_natMax]
      exact Order.le_max_left _ _
    have rightStartBound : rightStart ≤ rightFloor := by
      dsimp only [rightFloor]
      rewrite [Order.max_eq_natMax]
      exact Order.le_max_left _ _
    have leftJoinBound : join.comparison.leftIndex ≤ leftFloor := by
      dsimp only [leftFloor]
      rewrite [Order.max_eq_natMax]
      exact Order.le_max_right _ _
    have rightJoinBound : join.comparison.rightIndex ≤ rightFloor := by
      dsimp only [rightFloor]
      rewrite [Order.max_eq_natMax]
      exact Order.le_max_right _ _
    have leftFloorBound : leftFloor ≤ max leftFloor leftResidual := by
      rewrite [Order.max_eq_natMax]
      exact Order.le_max_left _ _
    have rightFloorBound : rightFloor ≤ max rightFloor rightResidual := by
      rewrite [Order.max_eq_natMax]
      exact Order.le_max_left _ _
    have leftResidualBound : leftResidual ≤ max leftFloor leftResidual := by
      rewrite [Order.max_eq_natMax]
      exact Order.le_max_right _ _
    have rightResidualBound : rightResidual ≤ max rightFloor rightResidual := by
      rewrite [Order.max_eq_natMax]
      exact Order.le_max_right _ _
    refine
      { leftIndex := max leftFloor leftResidual
        rightIndex := max rightFloor rightResidual
        left_ge := leftStartBound.trans leftFloorBound
        right_ge := rightStartBound.trans rightFloorBound
        close := ?_ }
    intro leftLater rightLater leftOrder rightOrder
    have leftBound := CertifiedSquareRoot.sample_residual_lt_of_index left.track residualTarget residualPositive
      leftLater (leftResidualBound.trans leftOrder)
    have rightBound := CertifiedSquareRoot.sample_residual_lt_of_index right.track residualTarget residualPositive
      rightLater (rightResidualBound.trans rightOrder)
    have close := join.comparison.close
      (leftJoinBound.trans (leftFloorBound.trans leftOrder))
      (rightJoinBound.trans (rightFloorBound.trans rightOrder))
    rewrite [Norm.Basic.normSq_eq_canonical] at close
    have near := close.le.trans
      (Fraction.Order.Field.divide_le_self join.leftTail.lower_positive.le
        (by decide +kernel : (1 : Fraction.Rational) ≤ 1024))
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact SquareRootChannelOwnership.root_distance join.leftTail.lower_positive
      (join.leftTail.lower_bound leftLater) near leftBound rightBound

/-- The original joined owners name the same signed root at arbitrary requested accuracy.

The actual retained raw comparison supplies the all-accuracy relation. The
original raw-to-named transport keeps both input tracks and apartness
preparations; no owner or preparation is reconstructed for this link.
-/
def equivalent (join : OwnerJoin left right) : Equivalence.NamedEquivalent (ownerName left) (ownerName right) :=
  SquareRootTrackEquivalence.rootEquivalent_of_approximationEquivalent
    left.parameterNonzero left.track right.track join.approximationEquivalent

end Equivalence

end OwnerJoin

end Purelib.Riemann.Paths.OwnerTraceReadings
