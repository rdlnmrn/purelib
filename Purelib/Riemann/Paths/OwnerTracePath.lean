module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Riemann.RootContinuation.SquareRootTrace
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Polygon.Basic

public import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Nat.Coprime.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

@[expose] public section

/-!
# Shared readings along finite owner trace paths

Each link accepts every pair of actual owner readings beyond two finite
thresholds.  The finite path fold chooses a shared vertex index large enough
for its two incident links, samples that owner once, and reuses the cached
value, norm, and residual in both certificates.
-/

namespace Purelib.Riemann.Paths.OwnerTracePath

open Purelib.Data.Rat.Fraction.Order

open Purelib.Riemann.Paths.OwnerTraceReadings

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense

open Purelib.Riemann.RootContinuation.SquareRootTrace

open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- A retained original owner tail together with one cached reading of that exact tail.

The original tail and its exact approximation index remain attached to the same root owner. The reading retains its
actual value, norm and residual caches with their original specification equalities. -/
structure OwnerReading {parameter : Basic.Canonical} (owner : Owner parameter) where
  /-- The retained certified tail of the exact original owner. -/ tail : OwnerTail owner
  /-- The cached original approximation reading belonging to that retained tail. -/ reading : OwnerTail.Reading tail

constructive_injectivity OwnerReading

namespace OwnerReading

variable {parameter : Data.Gaussian.Basic.Canonical} {owner : Owner parameter}

/-- The exact cached Gaussian value of the retained owner reading. -/
abbrev value (sample : OwnerReading owner) : Gaussian := sample.reading.value
/-- The exact original approximation index of the retained owner reading. -/
abbrev index (sample : OwnerReading owner) : Nat := sample.reading.index

/-- View the same cached original owner reading in another retained tail using an explicit later-index witness.

The value, norm and residual caches are reused unchanged; only the certified tail index relation is supplied anew. -/
def inTail (sample : OwnerReading owner) (tail : OwnerTail owner)
    (later : tail.first ≤ sample.index) : OwnerTail.Reading tail where
  index := sample.index
  later := later
  value := sample.value
  value_eq := sample.reading.value_eq
  norm := sample.reading.norm
  norm_eq := sample.reading.norm_eq
  residualNorm := sample.reading.residualNorm
  residualNorm_eq := sample.reading.residualNorm_eq

end OwnerReading

open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- A retained link between two original root owners with separate tail thresholds and a certified trace-edge
realization.

Every pair of readings beyond the two exact thresholds produces an edge over the original start and finish points,
preserving both owners and cached tails. -/
structure OwnerLink (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (start
  finish : Basic.Canonical)
    (left : Owner (polynomial.eval start)) (right : Owner (polynomial.eval finish)) where
  /-- The retained original left-owner approximation tail. -/ leftTail : OwnerTail left
  /-- The retained original right-owner approximation tail. -/ rightTail : OwnerTail right
  /-- The exact lower reading index required on the original left tail. -/ leftIndex : Nat
  /-- The exact lower reading index required on the original right tail. -/ rightIndex : Nat
  /-- The left reading threshold is no earlier than the original left tail start. -/ left_ge : leftTail.first ≤
    leftIndex
  /-- The right reading threshold is no earlier than the original right tail start. -/ right_ge : rightTail.first ≤
    rightIndex
  /-- Every pair of retained readings beyond both thresholds yields a certified edge over the original base endpoints.
  -/
  realize : ∀ (first : OwnerTail.Reading leftTail) (second : OwnerTail.Reading rightTail),
    leftIndex ≤ first.index → rightIndex ≤ second.index →
      Edge polynomial first.value second.value start finish

constructive_injectivity OwnerLink

namespace OwnerLink

open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
/-- Construct a same-base-point owner link from the two original tails and comparison indices retained by an owner join.
-/
def stationary (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (point :
  Basic.Canonical)
    {left right : Owner (polynomial.eval point)} (join : OwnerJoin left right) :
    OwnerLink polynomial point point left right where
  leftTail := join.leftTail
  rightTail := join.rightTail
  leftIndex := join.comparison.leftIndex
  rightIndex := join.comparison.rightIndex
  left_ge := join.comparison.left_ge
  right_ge := join.comparison.right_ge
  realize := join.stationaryEdge polynomial point

section
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic.Canonical (normSq)
open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Gaussian

/-- Build the actual moving link from two retained original tails in the same paid prepared-source box.

Every future realization consumes the supplied readings' original norm and
residual caches. The complete base-variation polynomial and movement budget
come from the supplied original EdgeData; no Horner, Reading or sample
producer is rerun. The actual target owner is retained as an input index.
-/
def ofRefiningBox {polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial}
    {baseStart baseFinish oldFirst oldLast : Basic.Canonical}
    {left : Owner (polynomial.eval baseStart)} {right : Owner (polynomial.eval baseFinish)}
    (data : EdgeData polynomial oldFirst oldLast baseStart baseFinish)
    (leftTail : OwnerTail left) (rightTail : OwnerTail right)
    (lower : Fraction.Rational) (positive : 0 < lower)
    (lowerBound : ∀ index : Nat, lower ≤ Norm.Basic.normSq ((ownerApproximation left).sample index))
    (refines : right.track.initial.box.Refines left.track.initial.box)
    (diameter : left.track.initial.box.diagonalSq ≤ lower / 1024)
    (movement : data.movementBound ≤ lower ^ 2 / 1024) :
    OwnerLink polynomial baseStart baseFinish left right where
  leftTail := leftTail
  rightTail := rightTail
  leftIndex := leftTail.first
  rightIndex := rightTail.first
  left_ge := Nat.le_refl _
  right_ge := Nat.le_refl _
  realize := by
    intro first second _ _
    have normLower : lower ≤ first.norm := by
      rewrite [first.norm_eq, first.value_eq]
      have bound := lowerBound first.index
      rewrite [Norm.Basic.normSq_eq_canonical] at bound
      exact bound
    have firstInside := left.certificate_candidate_in_initial_box left.parameterNonzero leftTail.state first.possible
    have secondInside := right.certificate_candidate_in_initial_box
      right.parameterNonzero rightTail.state second.possible
    have distance : normSq (second.value - first.value) ≤ first.norm / 1024 := by
      have bound := ((Geometry.Rational.Box.normSq_sub_le_diagonalSq
        (refines.contains secondInside) firstInside).trans diameter).trans
        (Fraction.Order.Field.divide_mono normLower (by decide +kernel))
      rewrite [Norm.Basic.normSq_eq_canonical] at bound
      exact bound
    refine ⟨data.withRootCaches first.value second.value first.norm first.norm_eq
      first.residualNorm first.residualNorm_eq, positive.trans_le normLower, distance, first.residual_small, ?_⟩
    exact movement.trans (Fraction.Order.Field.divide_mono
      (Arithmetic.pow_le_pow_direct positive.le normLower 2) (by decide +kernel))

end

end OwnerLink

open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- An ordered chain of retained links between exact original root owners over the base polynomial path.

The original start, intermediate and finish owners remain dependent indices, so concatenation preserves both geometric
points and owner identities. -/
inductive OwnerPath (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) :
    (start : Basic.Canonical) → Owner (polynomial.eval start) →
      (finish : Basic.Canonical) → Owner (polynomial.eval finish) → Type
  /-- An empty owner path retains one exact original point and its root owner. -/ | nil (point : Basic.Canonical) (owner
    : Owner (polynomial.eval point)) : OwnerPath polynomial point owner point owner
  /-- Prepend the retained link to the original owner path at its exact shared point and owner. -/ | cons {start middle
    finish : Basic.Canonical}
      {left : Owner (polynomial.eval start)} {center : Owner (polynomial.eval middle)}
      {right : Owner (polynomial.eval finish)}
      (edge : OwnerLink polynomial start middle left center)
      (tail : OwnerPath polynomial middle center finish right) : OwnerPath polynomial start left finish right

constructive_injectivity OwnerPath

namespace OwnerPath

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}

section
open Purelib.Data.Gaussian
/-- Transport a retained owner path along exact endpoint equalities and heterogeneous equalities of its original owners.
-/
def castEndpoints {start finish nextStart nextFinish : Basic.Canonical}
    {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}
    {nextLeft : Owner (polynomial.eval nextStart)} {nextRight : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (leftEq : HEq left nextLeft) (rightEq : HEq right nextRight)
    (path : OwnerPath polynomial start left finish right) :
    OwnerPath polynomial nextStart nextLeft nextFinish nextRight := by
  cases startEq
  cases finishEq
  cases eq_of_heq leftEq
  cases eq_of_heq rightEq
  exact path

/-- The ordered original base vertices reached by the retained owner links. -/
def vertices : ∀ {start finish : Basic.Canonical} {left : Owner (polynomial.eval start)}
    {right : Owner (polynomial.eval finish)}, OwnerPath polynomial start left finish right → List Basic.Canonical
  | _, _, _, _, .nil _ _ => []
  | _, _, _, _, .cons (middle := middle) _ tail => middle :: tail.vertices

/-- Transporting retained endpoint and owner identities preserves the exact original vertex list. -/
theorem castEndpoints_vertices {start finish nextStart nextFinish : Basic.Canonical}
    {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}
    {nextLeft : Owner (polynomial.eval nextStart)} {nextRight : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (leftEq : HEq left nextLeft) (rightEq : HEq right nextRight)
    (path : OwnerPath polynomial start left finish right) :
    (path.castEndpoints startEq finishEq leftEq rightEq).vertices = path.vertices := by
  cases startEq
  cases finishEq
  cases eq_of_heq leftEq
  cases eq_of_heq rightEq
  rfl

end

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
/-- The retained owner path's original vertex list terminates at its exact finish point. -/
theorem vertices_terminal : ∀ {start finish : Basic.Canonical} {left : Owner (polynomial.eval start)}
    {right : Owner (polynomial.eval finish)} (path : OwnerPath polynomial start left finish right),
    Polygon.Chain.terminal start path.vertices = finish
  | _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, .cons _ tail => tail.vertices_terminal

section
open Purelib.Data.Gaussian
/-- Transport a retained path along exact equalities of its original start and finish owners. -/
def reindexOwners {start finish : Basic.Canonical}
    {left nextLeft : Owner (polynomial.eval start)}
    {right nextRight : Owner (polynomial.eval finish)}
    (leftEq : left = nextLeft) (rightEq : right = nextRight)
    (path : OwnerPath polynomial start left finish right) :
    OwnerPath polynomial start nextLeft finish nextRight :=
  path.castEndpoints rfl rfl (heq_of_eq leftEq) (heq_of_eq rightEq)

/-- Reindexing equal retained endpoint owners preserves the exact original vertex list. -/
theorem reindexOwners_vertices {start finish : Basic.Canonical}
    {left nextLeft : Owner (polynomial.eval start)}
    {right nextRight : Owner (polynomial.eval finish)}
    (leftEq : left = nextLeft) (rightEq : right = nextRight)
    (path : OwnerPath polynomial start left finish right) :
    (path.reindexOwners leftEq rightEq).vertices = path.vertices :=
  path.castEndpoints_vertices rfl rfl (heq_of_eq leftEq) (heq_of_eq rightEq)

/-- Concatenate two retained owner paths at their exact shared middle point and original owner. -/
def append : ∀ {start middle finish : Basic.Canonical} {left : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)} {right : Owner (polynomial.eval finish)},
    OwnerPath polynomial start left middle center → OwnerPath polynomial middle center finish right →
      OwnerPath polynomial start left finish right
  | _, _, _, _, _, _, .nil _ _, second => second
  | _, _, _, _, _, _, .cons edge tail, second => .cons edge (tail.append second)

/-- The original vertices of concatenated retained owner paths are the ordered concatenation of their vertex lists. -/
theorem append_vertices : ∀ {start middle finish : Basic.Canonical} {left : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)} {right : Owner (polynomial.eval finish)}
    (first : OwnerPath polynomial start left middle center) (second : OwnerPath polynomial middle center finish right),
    (first.append second).vertices = first.vertices ++ second.vertices
  | _, _, _, _, _, _, .nil _ _, _ => rfl
  | _, _, _, _, _, _, .cons _ tail, second => by
      change _ :: (tail.append second).vertices = _ :: (tail.vertices ++ second.vertices)
      rw [append_vertices tail second]

/-- Appending the exact original stationary finish preserves the entire retained owner path. -/
theorem append_nil {start finish : Basic.Canonical}
    {source : Owner (polynomial.eval start)} {target : Owner (polynomial.eval finish)}
    (path : OwnerPath polynomial start source finish target) : path.append (.nil finish target) = path := by
  induction path with
  | nil => rfl
  | cons edge tail inductionHypothesis => exact congrArg (OwnerPath.cons edge) inductionHypothesis

/-- The original dependent owner-path concatenation associates without replacing any retained link. -/
theorem append_assoc {first second third fourth : Basic.Canonical}
    {firstOwner : Owner (polynomial.eval first)} {secondOwner : Owner (polynomial.eval second)}
    {thirdOwner : Owner (polynomial.eval third)} {fourthOwner : Owner (polynomial.eval fourth)}
    (left : OwnerPath polynomial first firstOwner second secondOwner)
    (middle : OwnerPath polynomial second secondOwner third thirdOwner)
    (right : OwnerPath polynomial third thirdOwner fourth fourthOwner) :
    (left.append middle).append right = left.append (middle.append right) := by
  induction left with
  | nil => rfl
  | cons edge tail inductionHypothesis =>
      exact congrArg (OwnerPath.cons edge) (inductionHypothesis middle)

/-- An exact prefix and suffix of one retained original owner path at their actual shared owner.

The original links and endpoint owners remain indexed by the supplied path.
Concatenating the retained pieces recovers that complete original value.
-/
def Split {start finish : Basic.Canonical}
    {source : Owner (polynomial.eval start)} {target : Owner (polynomial.eval finish)}
    (path : OwnerPath polynomial start source finish target) : Type :=
  Σ point : Basic.Canonical, Σ owner : Owner (polynomial.eval point),
  Σ initial : OwnerPath polynomial start source point owner,
    {suffix : OwnerPath polynomial point owner finish target // initial.append suffix = path}

namespace Split

variable {start finish : Basic.Canonical}
variable {source : Owner (polynomial.eval start)} {target : Owner (polynomial.eval finish)}
variable {path : OwnerPath polynomial start source finish target}

/-- Read the actual shared geometric endpoint of the two original path pieces. -/
def point (split : Split path) : Basic.Canonical := split.1

/-- Read the same original root owner at the retained split endpoint. -/
def owner (split : Split path) : Owner (polynomial.eval split.point) := split.2.1

/-- Read the retained original links preceding this exact owner occurrence. -/
def initial (split : Split path) : OwnerPath polynomial start source split.point split.owner := split.2.2.1

/-- Read the literal retained original suffix at this owner occurrence. -/
def remaining (split : Split path) : OwnerPath polynomial split.point split.owner finish target := split.2.2.2.val

/-- Concatenating both retained pieces recovers the complete supplied original owner path. -/
theorem append_eq (split : Split path) : split.initial.append split.remaining = path := split.2.2.2.property

/-- Every retained prefix vertex occurs in the same original whole path. -/
theorem prefix_member (split : Split path) (point : Basic.Canonical) (member : point ∈ split.initial.vertices) :
    point ∈ path.vertices := by
  have combined : point ∈ split.initial.vertices ++ split.remaining.vertices :=
    Purelib.Data.List.Membership.mem_append.mpr (Or.inl member)
  rewrite [← append_vertices, split.append_eq] at combined
  exact combined

end Split

/-- Split the actual original path after the requested number of retained links.

The recursion consumes the supplied link objects and returns its original
remaining tail literally. Requests beyond the final link retain the same
actual terminal owner. No root, tail, observation or comparison is acquired.
-/
def splitAt : (steps : Nat) → ∀ {start finish : Basic.Canonical}
    {source : Owner (polynomial.eval start)} {target : Owner (polynomial.eval finish)}
    (path : OwnerPath polynomial start source finish target), Split path
  | 0, start, _, source, _, path => ⟨start, source, .nil start source, ⟨path, rfl⟩⟩
  | _ + 1, _, _, _, _, .nil point owner => ⟨point, owner, .nil point owner, ⟨.nil point owner, rfl⟩⟩
  | steps + 1, _, _, _, _, .cons edge tail =>
      let rest := splitAt steps tail
      ⟨rest.point, rest.owner, .cons edge rest.initial,
        ⟨rest.remaining, congrArg (OwnerPath.cons edge) rest.append_eq⟩⟩

/-- Exact endpoint transport preserves the split's actual intermediate point and whole original owner.

Only the supplied endpoint equalities and complete heterogeneous owner
identities are eliminated. No path link or cached observation is replaced.
-/
theorem splitAt_castEndpoints {start finish nextStart nextFinish : Basic.Canonical}
    {source : Owner (polynomial.eval start)} {target : Owner (polynomial.eval finish)}
    {nextSource : Owner (polynomial.eval nextStart)} {nextTarget : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (sourceEq : HEq source nextSource) (targetEq : HEq target nextTarget)
    (path : OwnerPath polynomial start source finish target) (steps : Nat) :
    ((path.castEndpoints startEq finishEq sourceEq targetEq).splitAt steps).point = (path.splitAt steps).point ∧
      HEq ((path.castEndpoints startEq finishEq sourceEq targetEq).splitAt steps).owner (path.splitAt steps).owner := by
  cases startEq
  cases finishEq
  cases eq_of_heq sourceEq
  cases eq_of_heq targetEq
  exact ⟨rfl, HEq.rfl⟩

/-- Splitting within the first original path keeps its same point and nominal owner after concatenation. -/
theorem splitAt_append_left : ∀ (steps : Nat) {start middle finish : Basic.Canonical}
    {source : Owner (polynomial.eval start)} {center : Owner (polynomial.eval middle)}
    {target : Owner (polynomial.eval finish)} (first : OwnerPath polynomial start source middle center)
    (last : OwnerPath polynomial middle center finish target), steps ≤ first.vertices.length →
      ((first.append last).splitAt steps).point = (first.splitAt steps).point ∧
        HEq ((first.append last).splitAt steps).owner (first.splitAt steps).owner
  | 0, _, _, _, _, _, _, _, _, _ => ⟨rfl, HEq.rfl⟩
  | _ + 1, _, _, _, _, _, _, .nil _ _, _, bounded => False.elim (Nat.not_succ_le_zero _ bounded)
  | steps + 1, _, _, _, _, _, _, .cons _ rest, last, bounded =>
      splitAt_append_left steps rest last (Nat.le_of_succ_le_succ bounded)

/-- Splitting after the first original path reads the same retained suffix point and nominal owner. -/
theorem splitAt_append_right {start middle finish : Basic.Canonical}
    {source : Owner (polynomial.eval start)} {center : Owner (polynomial.eval middle)}
    {target : Owner (polynomial.eval finish)} (first : OwnerPath polynomial start source middle center)
    (last : OwnerPath polynomial middle center finish target) (steps : Nat) :
    ((first.append last).splitAt (first.vertices.length + steps)).point = (last.splitAt steps).point ∧
      HEq ((first.append last).splitAt (first.vertices.length + steps)).owner (last.splitAt steps).owner := by
  induction first with
  | nil =>
      change (last.splitAt (0 + steps)).point = (last.splitAt steps).point ∧
        HEq (last.splitAt (0 + steps)).owner (last.splitAt steps).owner
      rewrite [Nat.zero_add]
      exact ⟨rfl, HEq.rfl⟩
  | cons edge rest ih =>
      have offset : (rest.vertices.length + 1) + steps = (rest.vertices.length + steps) + 1 := by
        rewrite [Nat.add_assoc, Nat.add_comm 1 steps, ← Nat.add_assoc]
        rfl
      change ((OwnerPath.cons edge (rest.append last)).splitAt ((rest.vertices.length + 1) + steps)).point = _ ∧
        HEq ((OwnerPath.cons edge (rest.append last)).splitAt ((rest.vertices.length + 1) + steps)).owner _
      rewrite [offset]
      exact ih last

end

open Purelib.Data.Gaussian in
/-- Read the original terminal tail from the actual retained owner links.

The empty branch returns the supplied source tail literally. Every nonempty
branch passes the same cached right tail into the remaining path; no tail
acquisition, root preparation or numerical request is performed.
-/
def terminalTail : ∀ {start finish : Basic.Canonical} {source : Owner (polynomial.eval start)}
    {target : Owner (polynomial.eval finish)}, OwnerPath polynomial start source finish target →
    OwnerTail source → OwnerTail target
  | _, _, _, _, .nil _ _, sourceTail => sourceTail
  | _, _, _, _, .cons edge rest, _ => terminalTail rest edge.rightTail

open Purelib.Data.Gaussian in
/-- The empty path preserves the complete supplied source-tail cache. -/
theorem terminalTail_nil (point : Basic.Canonical) (owner : Owner (polynomial.eval point))
    (tail : OwnerTail owner) : (OwnerPath.nil point owner).terminalTail tail = tail := rfl

open Purelib.Data.Gaussian in
/-- A nonempty path reads the same stored right tail of its actual first link. -/
theorem terminalTail_cons {start middle finish : Basic.Canonical}
    {source : Owner (polynomial.eval start)} {center : Owner (polynomial.eval middle)}
    {target : Owner (polynomial.eval finish)}
    (edge : OwnerLink polynomial start middle source center)
    (rest : OwnerPath polynomial middle center finish target) (tail : OwnerTail source) :
    (OwnerPath.cons edge rest).terminalTail tail = rest.terminalTail edge.rightTail := rfl

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
set_option genInjectivity false in
/-- A retained sampled root trace realizing the original owner path beyond separate endpoint index floors.

The first and last readings keep their original owners and caches; the paired trace uses the exact original base
vertices and terminates at the retained last reading. -/
structure Realization {start finish : Basic.Canonical} {left : Owner (polynomial.eval start)}
    {right : Owner (polynomial.eval finish)} (path : OwnerPath polynomial start left finish right)
    (startMinimum finishMinimum : Nat) where
  /-- The retained original starting-owner reading of the realized trace. -/ first : OwnerReading left
  /-- The retained original finishing-owner reading of the realized trace. -/ last : OwnerReading right
  /-- The retained first reading index satisfies the supplied original start floor. -/ first_ge : startMinimum ≤
    first.index
  /-- The retained last reading index satisfies the supplied original finish floor. -/ last_ge : finishMinimum ≤
    last.index
  /-- The ordered retained root values paired with the original path vertices. -/ roots : List Basic.Canonical
  /-- The certified paired trace uses the retained first root and exact original base vertex list. -/ chain : Chain
    polynomial first.value roots start path.vertices
  /-- The retained root list terminates at exactly the cached last reading value. -/ terminal_root :
    Polygon.Chain.terminal first.value roots = last.value

constructive_injectivity Realization

open Purelib.Data.Gaussian in
open Purelib.Data in
/-- Realize the original owner path while reusing its retained link tails and satisfying both endpoint index floors.

The empty case selects one reading beyond both floors and the supplied tail start. Each nonempty step reuses its
original tails, recursively selected next reading and retained edge realization. -/
def realizeFromTail : ∀ {start finish : Basic.Canonical} {left : Owner (polynomial.eval start)}
    {right : Owner (polynomial.eval finish)} (path : OwnerPath polynomial start left finish right)
    (_incoming : OwnerTail left) (startMinimum finishMinimum : Nat), Realization path startMinimum finishMinimum
  | _, _, _, _, .nil point owner, tail, startMinimum, finishMinimum =>
      let index := max (max startMinimum finishMinimum) tail.first
      have tailBound : tail.first ≤ index := by
        dsimp only [index]
        rw [Nat.Order.max_eq_natMax]
        exact Nat.Order.le_max_right _ _
      have floorBound : max startMinimum finishMinimum ≤ index := by
        dsimp only [index]
        rw [Nat.Order.max_eq_natMax]
        exact Nat.Order.le_max_left _ _
      have startBound : startMinimum ≤ max startMinimum finishMinimum := by
        rw [Nat.Order.max_eq_natMax]
        exact Nat.Order.le_max_left _ _
      have finishBound : finishMinimum ≤ max startMinimum finishMinimum := by
        rw [Nat.Order.max_eq_natMax]
        exact Nat.Order.le_max_right _ _
      let reading := OwnerTail.Reading.acquire tail index tailBound
      let sample : OwnerReading owner := ⟨tail, reading⟩
      { first := sample
        last := sample
        first_ge := startBound.trans floorBound
        last_ge := finishBound.trans floorBound
        roots := []
        chain := .nil sample.value point
        terminal_root := rfl }
  | _, _, _, _, .cons edge tail, _incoming, startMinimum, finishMinimum =>
      let rest := realizeFromTail tail edge.rightTail edge.rightIndex finishMinimum
      let index := max startMinimum edge.leftIndex
      have startBound : startMinimum ≤ index := by
        dsimp only [index]
        rw [Nat.Order.max_eq_natMax]
        exact Nat.Order.le_max_left _ _
      have edgeBound : edge.leftIndex ≤ index := by
        dsimp only [index]
        rw [Nat.Order.max_eq_natMax]
        exact Nat.Order.le_max_right _ _
      let first := OwnerTail.Reading.acquire edge.leftTail index (edge.left_ge.trans edgeBound)
      let second := rest.first.inTail edge.rightTail (edge.right_ge.trans rest.first_ge)
      let certificate := edge.realize first second edgeBound rest.first_ge
      { first := ⟨edge.leftTail, first⟩
        last := rest.last
        first_ge := startBound
        last_ge := rest.last_ge
        roots := rest.first.value :: rest.roots
        chain := .cons certificate rest.chain
        terminal_root := rest.terminal_root }

open Purelib.Data.Gaussian in
/-- Produce a retained sampled trace of the original owner path beyond the supplied endpoint index floors.

A nonempty path reuses its first link's original tail; only an empty path acquires the original owner's tail directly.
-/
def realize {start finish : Basic.Canonical} {left : Owner (polynomial.eval start)}
    {right : Owner (polynomial.eval finish)} (path : OwnerPath polynomial start left finish right)
    (startMinimum finishMinimum : Nat) : Realization path startMinimum finishMinimum :=
  match path with
  | .nil point owner => realizeFromTail (.nil point owner) (OwnerTail.acquire owner) startMinimum finishMinimum
  | .cons edge tail => realizeFromTail (.cons edge tail) edge.leftTail startMinimum finishMinimum

section

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic.Canonical (normSq)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Approximation.Gaussian

/-- Every sufficiently synchronized original terminal sample stays near the same retained source reading.

The actual OwnerPath is realized beyond the two supplied floors using its
original link tails and cached readings. Fixed-reference confinement of
that realization and the target's original self-comparison control every
requested later sample, without selecting another target owner.
-/
theorem sample_near_reference {referenceParameter : Basic.Canonical}
    {referenceOwner : Owner referenceParameter} {referenceTail : OwnerTail referenceOwner}
    (reference : OwnerTail.Reading referenceTail)
    {start finish : Basic.Canonical} {source : Owner (polynomial.eval start)}
    {target : Owner (polynomial.eval finish)} (path : OwnerPath polynomial start source finish target)
    (sourceFloor : Nat)
    (sourceNear : ∀ index, sourceFloor ≤ index →
      normSq ((ownerApproximation source).sample index - reference.value) ≤ reference.norm / 16)
    (movement : ∀ point ∈ path.vertices,
      normSq (referenceParameter - polynomial.eval point) ≤ reference.norm ^ 2 / 1024)
    {leftStart rightStart : Nat}
    (comparison : Equivalence.Comparison (ownerApproximation target) (ownerApproximation target)
      leftStart rightStart (reference.norm / 64))
    (index : Nat) (leftLater : comparison.leftIndex ≤ index) (rightLater : comparison.rightIndex ≤ index) :
    normSq ((ownerApproximation target).sample index - reference.value) ≤ reference.norm / 4 := by
  have referencePositive : 0 < reference.norm := referenceTail.lower_positive.trans_le reference.lower
  have referenceNormPositive : 0 < normSq reference.value := by
    rewrite [← reference.norm_eq]
    exact referencePositive
  have referenceResidual := reference.residual_small
  rewrite [reference.residualNorm_eq, reference.norm_eq, pow_two] at referenceResidual
  let realized := path.realize sourceFloor index
  have firstNear : normSq (realized.first.value - reference.value) ≤ reference.norm / 16 := by
    change normSq (realized.first.reading.value - reference.value) ≤ reference.norm / 16
    rewrite [realized.first.reading.value_eq]
    exact sourceNear realized.first.index realized.first_ge
  have lastResidual := realized.last.reading.residual_small
  rewrite [realized.last.reading.residualNorm_eq, realized.last.reading.norm_eq] at lastResidual
  have terminalResidual : normSq ((Polygon.Chain.terminal realized.first.value realized.roots) ^ 2 -
      polynomial.eval (Polygon.Chain.terminal start path.vertices)) ≤
        normSq (Polygon.Chain.terminal realized.first.value realized.roots) ^ 2 / 1024 := by
    rewrite [realized.terminal_root, path.vertices_terminal]
    exact lastResidual
  have confined := realized.chain.terminal_near_reference referenceNormPositive referenceResidual
    (by rewrite [← reference.norm_eq]; exact firstNear)
    (fun point member => by
      have paid := movement point member
      rewrite [reference.norm_eq] at paid
      exact paid) terminalResidual
  rewrite [realized.terminal_root, ← reference.norm_eq] at confined
  have nearLast := comparison.close leftLater (rightLater.trans realized.last_ge)
  rewrite [← realized.last.reading.value_eq, Norm.Basic.normSq_eq_canonical] at nearLast
  have triangle := Norm.Bounds.normSq_sub_le_via
    ((ownerApproximation target).sample index) realized.last.value reference.value
  simp only [Norm.Basic.normSq_eq_canonical] at triangle
  calc
    _ ≤ 2 * (normSq ((ownerApproximation target).sample index - realized.last.value) +
        normSq (realized.last.value - reference.value)) := triangle
    _ ≤ 2 * (reference.norm / 64 + reference.norm / 16) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct nearLast.le confined) (by decide +kernel)
    _ = (2 * ((64 : Fraction.Rational)⁻¹ + (16 : Fraction.Rational)⁻¹)) * reference.norm := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ = (5 / 32 : Fraction.Rational) * reference.norm :=
      congrArg (fun coefficient : Fraction.Rational => coefficient * reference.norm) (by decide +kernel)
    _ ≤ (1 / 4 : Fraction.Rational) * reference.norm :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel) referencePositive.le
    _ = reference.norm / 4 := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1

open Purelib.Riemann.RootContinuation

/-- Compare the original terminal owners of two paid paths from one retained source join.

One cached source reading fixes the sign and all quantitative units. Each
requested comparison realizes the same two original paths and consumes their
actual terminal square-residual comparisons beyond both requested starts.
The uniform source floor pays movement along both vertex lists; no target
comparison, new root owner or successful search is supplied as a premise.
-/
def approximationEquivalent {start finish : Basic.Canonical}
    {firstSource secondSource : Owner (polynomial.eval start)}
    {firstTarget secondTarget : Owner (polynomial.eval finish)}
    (first : OwnerPath polynomial start firstSource finish firstTarget)
    (second : OwnerPath polynomial start secondSource finish secondTarget)
    (sourceJoin : OwnerJoin firstSource secondSource)
    (lower : Fraction.Rational) (positive : 0 < lower)
    (lowerBound : ∀ index, lower ≤ normSq ((ownerApproximation firstSource).sample index))
    (firstMovement : ∀ point ∈ first.vertices,
      normSq (polynomial.eval start - polynomial.eval point) ≤ lower ^ 2 / 1024)
    (secondMovement : ∀ point ∈ second.vertices,
      normSq (polynomial.eval start - polynomial.eval point) ≤ lower ^ 2 / 1024) :
    Equivalence.Equivalent (ownerApproximation firstTarget) (ownerApproximation secondTarget) := by
  let reference := sourceJoin.leftReading
  have referencePositive : 0 < reference.norm := sourceJoin.leftTail.lower_positive.trans_le reference.lower
  have floorLe : lower ≤ reference.norm := by
    rewrite [reference.norm_eq, reference.value_eq]
    exact lowerBound reference.index
  have movementPaid : lower ^ 2 / 1024 ≤ reference.norm ^ 2 / 1024 :=
    Fraction.Order.Field.divide_mono
      (Arithmetic.pow_le_pow_direct positive.le floorLe 2) (by decide +kernel)
  have firstNear : ∀ index, sourceJoin.comparison.leftIndex ≤ index →
      normSq ((ownerApproximation firstSource).sample index - reference.value) ≤ reference.norm / 16 := by
    intro index later
    have close := sourceJoin.sample_near_leftReading index later
    exact close.trans (by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      exact Arithmetic.mul_le_mul_of_nonneg_left_direct
        (by decide +kernel) referencePositive.le)
  have secondNear : ∀ index, sourceJoin.comparison.rightIndex ≤ index →
      normSq ((ownerApproximation secondSource).sample index - reference.value) ≤ reference.norm / 16 := by
    intro index later
    have close := sourceJoin.comparison.close (Nat.le_refl sourceJoin.comparison.leftIndex) later
    change Norm.Basic.normSq ((ownerApproximation firstSource).sample reference.index -
      (ownerApproximation secondSource).sample index) < _ at close
    rewrite [← reference.value_eq, Norm.Basic.normSq_eq_canonical] at close
    rewrite [show (ownerApproximation secondSource).sample index - reference.value =
      -(reference.value - (ownerApproximation secondSource).sample index) by ring1, Basic.Canonical.normSq_neg]
    calc
      _ ≤ sourceJoin.leftTail.lower / 1024 := close.le
      _ ≤ reference.norm / 1024 := Fraction.Order.Field.divide_mono reference.lower (by decide +kernel)
      _ ≤ reference.norm / 16 := by
        simp only [Fraction.Field.div_eq_mul_inv_direct]
        exact Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide +kernel) referencePositive.le
  exact SquareRootTrackEquivalence.approximationEquivalent_of_near_reference
    firstTarget.track secondTarget.track reference.value reference.norm reference.norm_eq referencePositive
    (by
      unfold SquareRootTrackEquivalence.NearReference
      intro leftStart rightStart comparison index leftLater rightLater
      exact first.sample_near_reference reference sourceJoin.comparison.leftIndex firstNear
        (fun point member => (firstMovement point member).trans movementPaid)
        comparison index leftLater rightLater)
    (by
      unfold SquareRootTrackEquivalence.NearReference
      intro leftStart rightStart comparison index leftLater rightLater
      exact second.sample_near_reference reference sourceJoin.comparison.rightIndex secondNear
        (fun point member => (secondMovement point member).trans movementPaid)
        comparison index leftLater rightLater)

end

end OwnerPath

namespace Chain

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- Concatenate retained paired root/base trace chains at their exact original terminal points. -/
def append {polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial} :
    ∀ {start baseStart : Basic.Canonical} {roots bases moreRoots moreBases : List Basic.Canonical},
      Chain polynomial start roots baseStart bases →
      Chain polynomial (Polygon.Chain.terminal start roots) moreRoots
        (Polygon.Chain.terminal baseStart bases) moreBases →
      Chain polynomial start (roots ++ moreRoots) baseStart (bases ++ moreBases)
  | _, _, [], [], _, _, .nil _ _, second => second
  | _, _, _ :: _, _ :: _, _, _, .cons edge tail, second => .cons edge (Chain.append tail second)

end Chain

namespace OwnerPath

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {base :
  Data.Gaussian.Basic.Canonical}
  {firstOwner lastOwner : Owner (polynomial.eval base)}

open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- A retained closed root trace over the exact original base vertices of a returning owner path.

The original ordered fields retain the same dependent source and target indices. Equality of the retained constructor is
characterized by its original field equalities, with all caches and relation witnesses preserved. -/
structure ClosedRealization (path : OwnerPath polynomial base firstOwner base lastOwner) where
  /-- The retained original starting-owner reading of the realized trace. -/ first : OwnerReading firstOwner
  /-- The ordered retained root values paired with the original path vertices. -/ roots : List Basic.Canonical
  /-- The retained certified closed root trace over the exact original base path vertices. -/ trace : Closed polynomial
    first.value roots base path.vertices

constructive_injectivity ClosedRealization

open Purelib.Geometry.Rational in
/-- Close the realized original owner path using the retained join from its last owner back to its first.

The join's exact comparison indices constrain the endpoint readings. One certified stationary base edge joins those
original readings while preserving the original path vertices. -/
def close (path : OwnerPath polynomial base firstOwner base lastOwner)
    (join : OwnerJoin lastOwner firstOwner) : ClosedRealization path := by
  let result := path.realize join.comparison.rightIndex join.comparison.leftIndex
  let finish := result.last.inTail join.leftTail (join.comparison.left_ge.trans result.last_ge)
  let start := result.first.inTail join.rightTail (join.comparison.right_ge.trans result.first_ge)
  let edge := join.stationaryEdge polynomial base finish start result.last_ge result.first_ge
  let closing : Chain polynomial
      (Polygon.Chain.terminal result.first.value result.roots) [result.first.value]
      (Polygon.Chain.terminal base path.vertices) [base] := by
    rw [result.terminal_root, path.vertices_terminal]
    exact .cons edge (.nil result.first.value base)
  exact ⟨result.first, result.roots, Chain.append result.chain closing⟩

open Purelib.Approximation.Gaussian in
open Purelib.Polynomial in
/-- A returning original owner path with equivalent final and initial root names cannot have odd base-polynomial
winding.

The retained name comparison closes the exact sampled root trace, whose winding certificate excludes raw winding equal
to four times an odd integer. -/
theorem not_odd_of_return (path : OwnerPath polynomial base firstOwner base lastOwner)
    (equivalent : Equivalence.NamedEquivalent (ownerName lastOwner) (ownerName firstOwner))
    (turns : Int) : Winding.Polygon.Basic.closedRaw polynomial base path.vertices ≠ 4 * (2 * turns + 1) := by
  let closed := path.close (OwnerJoin.acquire lastOwner firstOwner equivalent)
  exact (WindingComparison.build closed.trace).not_odd turns

end OwnerPath

end Purelib.Riemann.Paths.OwnerTracePath
