module
import Purelib.Data.Nat.Subtraction
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.Ring

public section

/-! Choose the source resampling mesh and reference depth before reading
fine samples. A single finite request pays every retained parent run. -/
section

open Purelib.Data.Rat
open Purelib.Data.List

open Purelib.Approximation
open Purelib.Curves
open Purelib.Geometry
open Purelib.Riemann

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine index :
    Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other target
    minimum}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

namespace SourceRunRefinement

/-- Compute the complete conjugate resampling scale from the squared parent count and source density. -/
@[expose] def sourceRunScale (count : Nat) (density : Normalization.InverseRootPolynomial.Coordinate) : Coordinate :=
  16 * (count : Normalization.InverseRootPolynomial.Coordinate)^2 * density^2

/-- The complete squared-count and squared-density resampling scale is nonnegative. -/
private theorem scale_nonnegative (count : Nat) (density : Normalization.InverseRootPolynomial.Coordinate) : 0 ≤
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement.sourceRunScale count density :=

  open Purelib.Data.Rat in Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
    decide) (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)

end SourceRunRefinement

namespace SourceRunRefinement

/-- The complete squared-count and squared-density resampling scale is nonnegative. -/
theorem scale_nonnegative_for_run (count : Nat) (density : Normalization.InverseRootPolynomial.Coordinate) : 0 ≤
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement.sourceRunScale count density :=

  open Purelib.Data.Rat in Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
    decide) (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)

end SourceRunRefinement

set_option genInjectivity false in
/-- A retained finite depth and positive width paying the complete source-run resampling target.

The exact geometric search result, minimum depth and quarter-radius bound certify the request before fine samples are
acquired. -/
structure SourceRunRefinement (count : Nat) (density target : Normalization.InverseRootPolynomial.Coordinate) (minimum :
  Nat) where
  /-- The retained reference depth selected by the original finite search. -/ depth : Nat
  /-- The retained depth is exactly the first qualifying quarter-radius search result. -/ depth_eq : depth =
    Rational.Geometric.Search.firstQuarterBelow
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement.sourceRunScale count density) minimum target
  /-- The selected depth pays the supplied minimum floor. -/ minimum_le : minimum ≤ depth
  /-- The cached common physical parameter-width cap. -/ width : Normalization.InverseRootPolynomial.Coordinate
  /-- The retained width is exactly the dyadic width at the selected depth. -/ width_eq : width = (1 / 2 :
    Normalization.InverseRootPolynomial.Coordinate)^depth
  /-- The retained physical width cap is strictly positive. -/ width_positive : 0 < width
  /-- The complete quarter-radius error at the selected depth is strictly below the target. -/ accurate :
    Rational.Geometric.Basic.quarterRadius
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement.sourceRunScale count density) depth < target

constructive_injectivity SourceRunRefinement

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement

/-- Compute the finite quarter-radius search and cache its certified depth and positive dyadic width. -/
@[expose] def build (count : Nat) (density target : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 <
  target) (minimum : Nat) :
    SourceRunRefinement count density target minimum :=
  open Purelib.Data.Rat in
  let depth := Rational.Geometric.Search.firstQuarterBelow
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement.sourceRunScale count density) minimum target
  { depth := depth, depth_eq := rfl
    minimum_le := Rational.Geometric.Search.firstQuarterBelow_ge _ _ _
    width := (1 / 2 : Normalization.InverseRootPolynomial.Coordinate)^depth, width_eq := rfl
    width_positive := Fraction.Order.Arithmetic.pow_pos_direct (by decide) _
    accurate := Rational.Geometric.Search.firstQuarterBelow_accurate _
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement.scale_nonnegative_for_run count density) _ _
      positive }

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement

/-- Increasing a natural depth decreases its rational dyadic width. -/
private theorem half_antitone {first last : Nat} (later : first ≤ last) :
    (1 / 2 : Normalization.InverseRootPolynomial.Coordinate)^last ≤ (1 / 2 :
      Normalization.InverseRootPolynomial.Coordinate)^first := open Purelib.Data.Rat in by
  let extra := last - first
  have reconstructed : last = first + extra := (Purelib.Data.Nat.Subtraction.add_sub_of_le later).symm
  rewrite [reconstructed]
  rw [pow_add]
  have bounded := Fraction.Order.Arithmetic.pow_le_pow_direct (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1 / 2)
    (by decide : (1 / 2 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1) extra
  rw [one_pow] at bounded
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded (Fraction.Order.Arithmetic.pow_nonneg_direct
    (by decide) first)).trans_eq (mul_one _)

/-- The squared dyadic width is the corresponding rational quarter power. -/
private theorem half_square (depth : Nat) :
    ((1 / 2 : Normalization.InverseRootPolynomial.Coordinate)^depth)^2 = (1 / 4 :
      Normalization.InverseRootPolynomial.Coordinate)^depth := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  exact congrArg (fun value : Normalization.InverseRootPolynomial.Coordinate => value^depth) (by
      decide : (1 / 2 : Normalization.InverseRootPolynomial.Coordinate)^2 = 1 / 4)

/-- A nonnegative bound on every original list entry bounds its zero-based finite maximum. -/
private theorem maximum_bounded {Item : Type u} (items : List Item) (value : Item →
  Normalization.InverseRootPolynomial.Coordinate)
    {bound : Normalization.InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ bound) (bounded : ∀ item ∈ items, value
      item ≤ bound) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum value items ≤ bound := by
  induction items with
  | nil => exact nonnegative
  | cons item rest ih =>
    exact Fraction.Order.Basic.max_le (bounded item List.mem_cons_self)
      (ih (fun next member => bounded next (List.mem_cons_of_mem _ member)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement

variable {count : Nat} {density requested : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement

/-- One local bound uses the cached physical width and the same later
reference depth; neither fine vertex counts nor resampled primitive values enter. -/
theorem run_error_bound (request : SourceRunRefinement
  count density requested floor)
    (run : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun plan sample otherSample
      fine)
    (densityLe : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity run.entry ≤ density)
      (widthLe : run.width ≤ request.width)
    (later : request.depth ≤ plan.parents.depth + fine) :
    run.error ≤ 16 * density^2 * request.width^2 := open Purelib.Data.Rat in by
  have sourceNonnegative : 0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity run.entry
    := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.sourceDensity_nonnegative _
  have square := Fraction.Order.Arithmetic.pow_le_pow_direct sourceNonnegative densityLe 2
  have maxNonnegative : 0 ≤ max run.width ((1 / 2 : Normalization.InverseRootPolynomial.Coordinate)^(plan.parents.depth
    + fine)) :=
    (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) _).trans (Fraction.Order.Basic.le_max_right _ _)
  have upper : max run.width ((1 / 2 : Normalization.InverseRootPolynomial.Coordinate)^(plan.parents.depth + fine)) ≤
    request.width :=
    Fraction.Order.Basic.max_le widthLe ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement.half_antitone
      later).trans_eq request.width_eq.symm)
  have widthSquare := Fraction.Order.Arithmetic.pow_le_pow_direct maxNonnegative upper 2
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square (by decide : (0 :
      Normalization.InverseRootPolynomial.Coordinate) ≤ 16)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthSquare (Fraction.Order.Arithmetic.mul_nonneg_direct
      (by decide) (Fraction.Order.Arithmetic.sq_nonneg_direct density)))

/-- The selected depth pays the full parent-count factor at every later
reference depth and every physical mesh satisfying the retained width cap. -/
theorem accurate_runs (request : SourceRunRefinement
  count density requested floor)
    (runs : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun plan sample
      otherSample fine)) (countLe : runs.length ≤ count)
    (densityLe : ∀ run ∈ runs, Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity run.entry
      ≤ density)
    (widthLe : ∀ run ∈ runs, run.width ≤ request.width)
    (later : request.depth ≤ plan.parents.depth + fine) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.conjugateSourceRunError runs < requested := open
      Purelib.Data.Rat in by
  have localNonnegative : 0 ≤ 16 * density^2 * request.width^2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have localBound := Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement.maximum_bounded runs
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.error localNonnegative
    (fun run member => request.run_error_bound run (densityLe run member) (widthLe run member) later)
  have lengthSquare := Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
    runs.length)) (Fraction.Cast.Order.natCast_le_direct countLe) 2
  have totalBound := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct localBound
    (Fraction.Order.Arithmetic.sq_nonneg_direct (runs.length : Normalization.InverseRootPolynomial.Coordinate))).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct lengthSquare localNonnegative)
  have scaleEq : (count : Normalization.InverseRootPolynomial.Coordinate)^2 * (16 * density^2 * request.width^2) =
      Rational.Geometric.Basic.quarterRadius
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement.sourceRunScale count density) request.depth :=
        by
    rw [request.width_eq, Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement.half_square,
      Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
    unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement.sourceRunScale
    ring1
  exact (totalBound.trans_eq scaleEq).trans_lt request.accurate

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement

/-- Uniform source density read from the existing parent plans, before any
fine source or cap sample is selected. -/
@[expose] def sourceRunDensity (plan :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other target minimum) :
  Coordinate :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum (fun parent => max parent.data.sourceSlope
    parent.otherData.sourceSlope) plan.parents.plans

/-- Choose a paid finite resampling request using the original parent-plan count and source-density bound. -/
@[expose] def sourceRunRefinement (plan :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other target minimum)
    (requested : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < requested) (floor : Nat) :
    SourceRunRefinement plan.parents.plans.length
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement.sourceRunDensity plan) requested floor :=
  build _ _ requested positive floor

/-- Parent ownership supplies both the count and density bounds internally.
Only the actual physical mesh width and later reference depth remain geometric inputs. -/
theorem sourceRunRefinement_accurate (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    {requested : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}
    (request : SourceRunRefinement
      plan.parents.plans.length (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement.sourceRunDensity plan)
      requested floor)
    (runs : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun plan sample
      otherSample fine))
    (ordered : runs.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.entry =
      evaluated.retained)
    (widthLe : ∀ run ∈ runs, run.width ≤ request.width)
    (later : request.depth ≤ plan.parents.depth + fine) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.conjugateSourceRunError runs < requested := open
      Purelib in by
  have countEq : runs.length = plan.parents.plans.length := by
    have first := congrArg List.length ordered
    have last := congrArg List.length evaluated.plans_eq
    rw [Map.length_map] at first last
    exact first.trans last
  apply request.accurate_runs runs countEq.le _ widthLe later
  intro run member
  have entryMember : run.entry ∈ evaluated.retained :=
    Eq.mp (congrArg (fun entries => run.entry ∈ entries) ordered)
      (Data.List.Map.mem_map_of_mem (f :=
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns.ResampledSourceRun.entry) member)
  have parentMember : run.entry.plan ∈ plan.parents.plans :=
    Eq.mp (congrArg (fun parents => run.entry.plan ∈ parents) evaluated.plans_eq)
      (Data.List.Map.mem_map_of_mem (f := fun entry => entry.plan) entryMember)
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum _ parentMember

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement

end
