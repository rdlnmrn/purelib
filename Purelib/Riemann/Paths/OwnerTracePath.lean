module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Riemann.RootContinuation.SquareRootTrace
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Geometry.Rational.Polygon.Chain
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
import Purelib.Data.Gaussian.Norm.Basic
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

variable {parameter : Purelib.Data.Gaussian.Basic.Canonical} {owner : Owner parameter}

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
structure OwnerLink (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (start
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
def stationary (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (point :
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

end OwnerLink

open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- An ordered chain of retained links between exact original root owners over the base polynomial path.

The original start, intermediate and finish owners remain dependent indices, so concatenation preserves both geometric
points and owner identities. -/
inductive OwnerPath (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
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

end

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

end OwnerPath

namespace Chain

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- Concatenate retained paired root/base trace chains at their exact original terminal points. -/
def append {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} :
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
  Purelib.Data.Gaussian.Basic.Canonical}
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
