module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure

public section

/-!
# Whole-component period allowances before exterior sampling

The original exterior programs supply the parent counts and movement masses.
These cached allowances let the segment requests be assembled later without
repeating their polynomial construction or changing any period parent.
-/

section

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open Purelib.Data.Rat
open Purelib.Riemann.Integration

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceComponent)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_nonnegative)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans

set_option genInjectivity false in
/-- Positive scalar period allowances on one actual retained exterior component.

The original parent list fixes the cached movement mass, local target and coefficient allowance before numerical segment
construction. -/
structure ComponentPeriodPlan (component : ExteriorProgram.SurfaceComponent regular domains differential) (target :
  InverseRootPolynomial.Coordinate) where
  /-- The original complete component target is strictly positive. -/ positive : 0 < target
  /-- The cached movement mass of the original exterior program parents. -/ mass : InverseRootPolynomial.Coordinate
  /-- The mass cache is exactly the original program's retained parent movement mass. -/ mass_eq : mass =
    PreparedRefinementMovement.movementMass component.program.cache.parents
  /-- The cached per-parent primitive accuracy target. -/ localTarget : InverseRootPolynomial.Coordinate
  /-- The local target is the aggregate allocation using the original component target and parent count. -/
    localTarget_eq : localTarget = Aggregate.perTerm target component.program.cache.parents.length
  /-- The retained local target or complete-bank minimum is strictly positive. -/ local_positive : 0 < localTarget
  /-- The cached coefficient-error allowance for the retained movement mass. -/ coefficient :
    InverseRootPolynomial.Coordinate
  /-- The coefficient allowance is half the original target divided by one plus the retained mass. -/ coefficient_eq :
    coefficient = (target / 2) / (mass + 1)
  /-- The retained coefficient allowance or complete-bank minimum is strictly positive. -/ coefficient_positive : 0 <
    coefficient

constructive_injectivity ComponentPeriodPlan

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlan

/-- Cache the actual original parent movement mass and both positive scalar allowances for this retained exterior
component. -/
@[expose] def build (component : ExteriorProgram.SurfaceComponent regular domains differential) (target :
  InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlan component target :=
  let mass := PreparedRefinementMovement.movementMass component.program.cache.parents
  let localTarget := Aggregate.perTerm target component.program.cache.parents.length
  let coefficient := (target / 2) / (mass + 1)
  ⟨positive, mass, rfl, localTarget, rfl, Aggregate.perTerm_positive positive _, coefficient, rfl,
    Fraction.Order.Field.div_pos_direct (Fraction.Order.Field.div_pos_direct positive (by decide))
      (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (PreparedRefinementMovement.movementMass_nonnegative _)
        (by decide))⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlan

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans

set_option genInjectivity false in
/-- The complete scalar plan spine on the actual retained exterior components. -/
inductive ComponentPeriodPlans (target : InverseRootPolynomial.Coordinate) : List (ExteriorProgram.SurfaceComponent
  regular domains differential) → Type 2
  /-- The empty original component list needs no scalar period plans. -/ | nil :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlans target []
  /-- Retain one actual component's scalar plan with the original remaining component plans. -/ | cons {component
    components} (head : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlan component
    target)
      (tail : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlans target
        components) : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlans target
        (component :: components)

constructive_injectivity ComponentPeriodPlans

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans

variable {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlans

/-- Cache one scalar period plan per actual original exterior component in retained order. -/
@[expose] def build (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    (components : List (ExteriorProgram.SurfaceComponent regular domains differential)) →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlans target components
  | [] => .nil
  | component :: components => .cons
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlan.build component target positive)
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlans.build target positive
    components)

/-- Read the positive common local allowance from the original component plans, bounded by one. -/
@[expose] def localMinimum : {components : List (ExteriorProgram.SurfaceComponent regular domains differential)} →
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlans target components →
  InverseRootPolynomial.Coordinate
  | _, .nil => 1
  | _, .cons head tail => min head.localTarget tail.localMinimum

/-- Read the positive common coefficient allowance from the original component plans, bounded by one. -/
@[expose] def coefficientMinimum : {components : List (ExteriorProgram.SurfaceComponent regular domains differential)} →
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlans target components →
  InverseRootPolynomial.Coordinate
  | _, .nil => 1
  | _, .cons head tail => min head.coefficient tail.coefficientMinimum

/-- The retained local target or complete-bank minimum is strictly positive. -/
theorem local_positive {components : List (ExteriorProgram.SurfaceComponent regular domains differential)} (plans :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlans target components) :
    0 < plans.localMinimum := by
  induction plans with
  | nil => change (0 : InverseRootPolynomial.Coordinate) < 1; decide
  | cons head tail ih => exact Fraction.Order.Basic.lt_min head.local_positive ih

/-- The retained coefficient allowance or complete-bank minimum is strictly positive. -/
theorem coefficient_positive {components : List (ExteriorProgram.SurfaceComponent regular domains differential)} (plans
  : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlans target components) :
    0 < plans.coefficientMinimum := by
  induction plans with
  | nil => change (0 : InverseRootPolynomial.Coordinate) < 1; decide
  | cons head tail ih => exact Fraction.Order.Basic.lt_min head.coefficient_positive ih

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPlans.ComponentPeriodPlans

end
