module
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial

public section

/-! Synchronize the physical source owners before sampling the common cap arcs. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data.Rat
open Purelib
open Purelib.Riemann

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

open Purelib.Data.Rat.Fraction.Compatibility

namespace PhysicalSourceRequest

/-- The same occurrence is shared by the physical source plan and its request. -/
@[expose] def PhysicalSourcePlans (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (other : Hyperelliptic.Differentials.Basic.Differential genus) (allowance : Fraction.Rational) (minimum : Nat) :=
  Data.Vector.DependentVector (fun i : Fin prepared.occurrences.length =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
      (prepared.occurrences[i.val]'i.isLt) other (allowance / 4) minimum)

end PhysicalSourceRequest

set_option genInjectivity false in
/-- Initial source plans and the aggregate error allocation. Physical owner
queries determine the final source floors and sampling schedule downstream. -/
structure PhysicalSourceRequest (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (other : Hyperelliptic.Differentials.Basic.Differential genus) (target : Fraction.Rational) (minimum floor : Nat)
      where
  /-- The retained common error allowance for every original surface occurrence. -/ allowance : Fraction.Rational
  /-- The retained allowance is exactly the finite aggregate allocation at the original occurrence count. -/
    allowance_eq : allowance = Rational.Budget.Aggregate.perTerm target prepared.occurrences.length
  /-- The common occurrence allowance is strictly positive. -/ positive : 0 < allowance
  /-- The squared original occurrence count pays the complete target strictly. -/ paid : (prepared.occurrences.length :
    Fraction.Rational) * ((prepared.occurrences.length : Fraction.Rational) * allowance) < target
  /-- The dependent source-plan bank indexed by the original surface occurrences. -/ plans :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSourceRequest.PhysicalSourcePlans prepared other allowance
    minimum
  /-- The cached common numerical source stage. -/ index : Nat
  /-- The cached stage is the maximum of the supplied minimum and all retained plan stages. -/ index_eq : index = max
    minimum (plans.maximum fun _ plan => plan.index)
  /-- Every original retained source plan is paid by the shared stage. -/ index_ge : ∀ i, (plans.get i).index ≤ index

constructive_injectivity PhysicalSourceRequest

namespace PhysicalSourceRequest
variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {target : Fraction.Rational} {minimum floor : Nat}

/-- Allocate the complete physical source budget and prepare the original occurrence-indexed source plans.

The finite aggregate allowance pays all original occurrences, and the retained maximum synchronizes their numerical
stages. -/
@[expose] def build (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential) (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (target : Fraction.Rational) (positive : 0 < target) (minimum floor : Nat) :
    PhysicalSourceRequest prepared other target
      minimum floor := by
  let allowance := Rational.Budget.Aggregate.perTerm target prepared.occurrences.length
  have allowancePositive := Rational.Budget.Aggregate.perTerm_positive positive prepared.occurrences.length
  let plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSourceRequest.PhysicalSourcePlans prepared other
    allowance minimum := Data.Vector.DependentVector.ofFn fun i =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.build prepared
      (prepared.occurrences[i.val]'i.isLt) (List.getElem_mem i.isLt)
      other (allowance / 4) (Fraction.Order.Field.div_pos_direct allowancePositive (by decide)) minimum
  let index := max minimum (plans.maximum fun _ plan => plan.index)
  refine ⟨allowance, rfl, allowancePositive, Rational.Budget.Aggregate.count_mul_perTerm_lt positive _,
    plans, index, rfl, ?_⟩
  intro i
  exact (plans.get_le_maximum (fun _ plan => plan.index) i).trans (Data.Nat.Order.le_max_right _ _)

end PhysicalSourceRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
