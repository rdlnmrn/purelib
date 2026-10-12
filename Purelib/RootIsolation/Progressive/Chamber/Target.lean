module

import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Stability
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Bezout
public import Purelib.Data.Rat.List.Minimum
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.Data.List.OfFn.Basic

/-!
# Common allowances for finite simple-root owner families

Every original bounded owner contributes its retained Bézout and boundary
allowances. Their finite ordered target list yields one positive common
allowance without changing owners, boxes or reference certificates.
-/

namespace Purelib.RootIsolation.Progressive.Chamber.Target

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.RootIsolation

open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table (CoefficientTable)

/-- Per-owner allowance targets which simultaneously retain the reference
Bézout separation and the owner's initial boundary clearance.

Each original bounded owner contributes the minimum of its reference
Bézout allowance and boundary-clearance allowance. The finite table retains
the original owner order and boxes. -/
@[expose] public def simpleRootOwnerTargets
    (reference : CoefficientTable)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate reference.polynomial)
    (owners : Owner.Family.Basic.OwnerFamily reference.polynomial reference.degree) :
    List Fraction.Rational :=
  List.ofFn fun index : Fin reference.degree =>
    min
      (reference.bezoutStabilityTarget squarefree
        (owners.owner index).box)
      (reference.stabilityTarget (owners.owner index).box
        (owners.owner index).clearance)

/-- One common positive allowance target for the complete finite owner
family.

The original positive-minimum operation reads the same complete finite
owner-target list. It supplies one rational target without changing any
owner, reference factor or boundary certificate. -/
@[expose] public def simpleRootChamberTarget
    (reference : CoefficientTable)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate reference.polynomial)
    (owners : Owner.Family.Basic.OwnerFamily reference.polynomial reference.degree) : Fraction.Rational :=
  Data.Rat.List.Minimum.positiveMinimum
    (Progressive.Chamber.Target.simpleRootOwnerTargets reference squarefree owners)

/-- The common chamber target fits the Bézout-stability allowance of every original owner.

The supplied original owner index witnesses membership of its retained
minimum target. The common positive minimum lies below that target and
therefore below the same owner Bézout allowance. -/
public theorem simpleRootChamberTarget_le_bezout
    (reference : CoefficientTable)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate reference.polynomial)
    (owners : Owner.Family.Basic.OwnerFamily reference.polynomial reference.degree)
    (index : Fin reference.degree) :
    Progressive.Chamber.Target.simpleRootChamberTarget reference squarefree owners ≤
      reference.bezoutStabilityTarget squarefree
        (owners.owner index).box := by
  have commonLe := Data.Rat.List.Minimum.positiveMinimum_le_of_mem
    (values := Progressive.Chamber.Target.simpleRootOwnerTargets reference squarefree owners)
    (value := min
      (reference.bezoutStabilityTarget squarefree
        (owners.owner index).box)
      (reference.stabilityTarget (owners.owner index).box
        (owners.owner index).clearance)) (by
      exact Data.List.OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩)
  exact commonLe.trans (Fraction.Order.Basic.min_le_left _ _)

/-- The common chamber target fits the boundary-stability allowance of every original owner.

The supplied original owner index witnesses membership of its retained
minimum target. The common positive minimum lies below that target and
therefore below the same owner boundary allowance. -/
public theorem simpleRootChamberTarget_le_stability
    (reference : CoefficientTable)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate reference.polynomial)
    (owners : Owner.Family.Basic.OwnerFamily reference.polynomial reference.degree)
    (index : Fin reference.degree) :
    Progressive.Chamber.Target.simpleRootChamberTarget reference squarefree owners ≤
      reference.stabilityTarget (owners.owner index).box
        (owners.owner index).clearance := by
  have commonLe := Data.Rat.List.Minimum.positiveMinimum_le_of_mem
    (values := Progressive.Chamber.Target.simpleRootOwnerTargets reference squarefree owners)
    (value := min
      (reference.bezoutStabilityTarget squarefree
        (owners.owner index).box)
      (reference.stabilityTarget (owners.owner index).box
        (owners.owner index).clearance)) (by
      exact Data.List.OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩)
  exact commonLe.trans (Fraction.Order.Basic.min_le_right _ _)

/-- Every retained per-owner chamber allowance is strictly positive.

A retained list member comes from an original bounded owner index.
Its reference Bézout and boundary targets are both strictly positive,
so their original minimum is strictly positive. -/
public theorem simpleRootOwnerTargets_positive
    (reference : CoefficientTable)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate reference.polynomial)
    (owners : Owner.Family.Basic.OwnerFamily reference.polynomial reference.degree) :
    ∀ target ∈ Progressive.Chamber.Target.simpleRootOwnerTargets reference squarefree owners,
      0 < target := by
  intro target member
  rcases Data.List.OfFn.Basic.mem_ofFn.mp member with ⟨index, rfl⟩
  exact Fraction.Order.Basic.lt_min
    (reference.bezoutStabilityTarget_pos squarefree
      (owners.owner index).box)
    (reference.stabilityTarget_pos (owners.owner index).box
      (owners.owner index).clearance)

/-- The common finite-owner chamber allowance is strictly positive.

Every target in the original finite owner list is positive. The retained
positive-minimum operation therefore gives a strictly positive common
chamber allowance. -/
public theorem simpleRootChamberTarget_pos
    (reference : CoefficientTable)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate reference.polynomial)
    (owners : Owner.Family.Basic.OwnerFamily reference.polynomial reference.degree) :
    0 < Progressive.Chamber.Target.simpleRootChamberTarget reference squarefree owners :=
  Data.Rat.List.Minimum.positiveMinimum_pos _
    (Progressive.Chamber.Target.simpleRootOwnerTargets_positive reference squarefree owners)

end Purelib.RootIsolation.Progressive.Chamber.Target
