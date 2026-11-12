module

public import Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport
public import Purelib.Riemann.RootContinuation.FixedRootBoxBudget.Stream
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.Fin.Two

/-! # Cofactor root streams on the original collision patch

The existing original reference owner retains clearance9/16 and its existing
half-quadrance budget. Actual spatial-patch sample containment pays every
cofactor movement; no final root comparison or new sheet selector is supplied.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (ofApproximation)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- The original signed reference radicand has exact unit quadrance at either node. -/
theorem source_normSq (site : Fin 2) : Norm.Basic.normSq (seed site ^ 2) = 1 := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- A GIVEN complete reference-owner cache retains the original signed source box. -/
theorem reference_box (site : Fin 2)
    (reference : { value : Owner (seed site ^ 2) // value = source site }) :
    reference.val.track.initial.box = box site :=
  (congrArg (fun value : Owner (seed site ^ 2) =>
    value.track.initial.box) reference.property).trans (source_box site)

/-- The SAME complete reference-owner cache retains the original clearance nine sixteenths. -/
theorem reference_bound (site : Fin 2)
    (reference : { value : Owner (seed site ^ 2) // value = source site }) :
    reference.val.track.initial.clearance.bound = 9 / 16 :=
  (congrArg (fun value : Owner (seed site ^ 2) =>
    value.track.initial.clearance.bound) reference.property).trans (source_bound site)

/-- Half-quadrance movement is strictly below the SAME retained reference owner's original clearance. -/
theorem half_lt_reference (site : Fin 2)
    (reference : { value : Owner (seed site ^ 2) // value = source site }) :
    (1 / 2 : Fraction.Rational) < reference.val.track.initial.clearance.bound := by
  rewrite [reference_bound site reference]
  decide +kernel

/-- Transport the original zero-exclusion side to the SAME retained reference-owner box. -/
def sourceSide (site : Fin 2)
    (reference : { value : Owner (seed site ^ 2) // value = source site }) :
    reference.val.track.initial.box.OutsideSide 0 :=
  (reference_box site reference).symm ▸ zeroSide site

/-- A GIVEN budget constructed on the actual retained reference owner has movement exactly one half. -/
theorem half_movement (site : Fin 2)
    (reference : { value : Owner (seed site ^ 2) // value = source site })
    (paid : { value : FixedRootBoxBudget.Budget reference.val // value = FixedRootBoxBudget.Budget.acquire
      reference.val (1 / 2) (by decide +kernel) (half_lt_reference site reference) }) :
    paid.val.movement = 1 / 2 :=
  congrArg (fun value : FixedRootBoxBudget.Budget reference.val => value.movement) paid.property

/-- The retained half-movement budget lies strictly below its original reference radicand quadrance. -/
theorem separated (site : Fin 2)
    (reference : { value : Owner (seed site ^ 2) // value = source site })
    (paid : { value : FixedRootBoxBudget.Budget reference.val // value = FixedRootBoxBudget.Budget.acquire
      reference.val (1 / 2) (by decide +kernel) (half_lt_reference site reference) }) :
    paid.val.movement < Norm.Basic.normSq (seed site ^ 2) := by
  rewrite [half_movement site reference paid, source_normSq]
  decide +kernel

/-- Actual patch geometry pays cofactor movement for the SAME budget, owner and radicand program. -/
theorem samples_movement (site : Fin 2) (base radicand : GeometricApproximation)
    (inside : ∀ index, (spatialBox site).Contains (base.sample index))
    (samples : ∀ index, radicand.sample index = (unitPolynomial site).eval (base.sample index))
    (reference : { value : Owner (seed site ^ 2) // value = source site })
    (paid : { value : FixedRootBoxBudget.Budget reference.val // value = FixedRootBoxBudget.Budget.acquire
      reference.val (1 / 2) (by decide +kernel) (half_lt_reference site reference) }) (index : Nat) :
    Norm.Basic.normSq (seed site ^ 2 - radicand.sample index) ≤ paid.val.movement :=
  (congrArg (fun value : Canonical => Norm.Basic.normSq (seed site ^ 2 - value)) (samples index)).trans_le
    ((variation_bound site (inside index)).trans_eq (half_movement site reference paid).symm)

/-- A patch stream retains the original owner, its actual acquired budget and the complete signed root stream. -/
@[expose] def PatchStream (site : Fin 2) (base radicand : GeometricApproximation)
    (inside : ∀ index, (spatialBox site).Contains (base.sample index))
    (samples : ∀ index, radicand.sample index = (unitPolynomial site).eval (base.sample index)) : Type _ :=
  (reference : { value : Owner (seed site ^ 2) // value = source site }) ×
  (paid : { value : FixedRootBoxBudget.Budget reference.val // value = FixedRootBoxBudget.Budget.acquire
    reference.val (1 / 2) (by decide +kernel) (half_lt_reference site reference) }) ×
  { value : FixedRootBoxBudget.Budget.Stream (original := reference.val) paid.val radicand
      (samples_movement site base radicand inside samples reference paid)
      (separated site reference paid) (sourceSide site reference) //
    value = FixedRootBoxBudget.Budget.stream (original := reference.val) paid.val radicand
      (samples_movement site base radicand inside samples reference paid)
      (separated site reference paid) (sourceSide site reference) }

/-- Construct one original owner, its actual half-movement budget and the GIVEN sample stream's signed root. -/
def fromSamples (site : Fin 2) (base radicand : GeometricApproximation)
    (inside : ∀ index, (spatialBox site).Contains (base.sample index))
    (samples : ∀ index, radicand.sample index = (unitPolynomial site).eval (base.sample index)) :
    PatchStream site base radicand inside samples := by
  let reference := source site
  let ownerCache : { value : Owner (seed site ^ 2) // value = source site } :=
    ⟨reference, rfl⟩
  let paid := FixedRootBoxBudget.Budget.acquire reference (1 / 2) (by decide +kernel)
    (half_lt_reference site ownerCache)
  let budgetCache : { value : FixedRootBoxBudget.Budget reference // value = FixedRootBoxBudget.Budget.acquire
      reference (1 / 2) (by decide +kernel) (half_lt_reference site ownerCache) } := ⟨paid, rfl⟩
  let roots := FixedRootBoxBudget.Budget.stream (original := reference) paid radicand
    (samples_movement site base radicand inside samples ownerCache budgetCache)
    (separated site ownerCache budgetCache) (sourceSide site ownerCache)
  exact ⟨ownerCache, budgetCache, ⟨roots, rfl⟩⟩

namespace PatchStream

variable {site : Fin 2} {base radicand : GeometricApproximation}
    {inside : ∀ index, (spatialBox site).Contains (base.sample index)}
    {samples : ∀ index, radicand.sample index = (unitPolynomial site).eval (base.sample index)}
    (actual : PatchStream site base radicand inside samples)

/-- Read the original root channel retained in the SAME complete patch stream. -/
@[expose] def root : CoherentNamed := actual.2.2.val.2.2.1.val

/-- Read the original square comparison of that SAME root with the GIVEN cofactor sample program. -/
def square : NamedEquivalent (actual.root.mul actual.root).name
    (ofApproximation radicand.toApproximation).name :=
  actual.2.2.val.2.2.2.1

/-- Every native sample of the SAME patch root lies in the original node's signed unit-root box. -/
theorem native_inside (index : Nat) :
    (box site).Contains ((Sampling.approximation actual.root.name).sample index) := by
  have boxed : actual.1.val.track.initial.box.Contains
      ((Sampling.approximation actual.root.name).sample index) :=
    FixedRootBoxBudget.Budget.Stream.native_inside
      (original := actual.1.val) (budget := actual.2.1.val) (radicand := radicand)
      (within := samples_movement site base radicand inside samples actual.1 actual.2.1)
      (separated := separated site actual.1 actual.2.1)
      (sourceSide site actual.1) actual.2.2.val.1.val actual.2.2.val.2.1 actual.2.2.val.2.2.1 index
  exact Eq.mp (congrArg (fun region : Purelib.Geometry.Rational.Box => region.Contains
    ((Sampling.approximation actual.root.name).sample index))
      (reference_box site actual.1)) boxed

end PatchStream

end Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport

end
