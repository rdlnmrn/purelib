module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.ReciprocalCapBilinearBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Integration.PreparedPairedParentCapReadback
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

public section

/-! One count-paid request for every retained exterior occurrence. Model
stages and literal inverse-arc depths are shared across the entire family. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

set_option genInjectivity false in
/-- One original exterior occurrence and its paired parent-area request at the retained local allowance. -/
structure PairedArcPlan (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (other : Hyperelliptic.Differentials.Basic.Differential genus) (allowance : Fraction.Rational) (minimum : Nat) where
  /-- The retained original exterior occurrence. -/ occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential
  /-- The occurrence belongs to the original prepared exterior list. -/ member : occurrence ∈ prepared.occurrences
  /-- The paired-area request on that occurrence's exact original parent cache. -/ parents :
    Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other
    occurrence.compared.entered.cache.parents allowance minimum

constructive_injectivity PairedArcPlan

namespace PairedArcPlan
variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {allowance : Fraction.Rational} {minimum : Nat}

/-- The original occurrence mesh depth plus its retained parent-area depth. -/
@[expose] def depth (plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan prepared other
  allowance minimum) : Nat := plan.occurrence.piece.mesh.depth + plan.parents.depth

/-- Prepare paired parent requests for the supplied original occurrences in order. -/
@[expose] def build (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential) (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (minimum : Nat) :
    (occurrences : List
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
      regular domains differential)) →
    (∀ occurrence ∈ occurrences, occurrence ∈ prepared.occurrences) → List
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan prepared other allowance minimum)
  | [], _ => []
  | occurrence :: tail, member =>
      ⟨occurrence, member occurrence List.mem_cons_self,
        occurrence.pairedAreaRequest prepared (member occurrence List.mem_cons_self) other allowance positive minimum⟩
          ::
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.build prepared other
          allowance positive minimum tail
          (fun occurrence retained => member occurrence (List.mem_cons_of_mem _ retained))

/-- The constructed plans retain exactly the supplied original occurrence list. -/
theorem build_occurrences (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential) (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (minimum : Nat)
    (occurrences : List
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
      regular domains differential))
    (member : ∀ occurrence ∈ occurrences, occurrence ∈ prepared.occurrences) :
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.build prepared other allowance positive
      minimum occurrences member).map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.occurrence = occurrences := by
  induction occurrences with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) (ih _)

/-- The finite maximum of retained plan indices or depths together with the supplied minimum. -/
@[expose] def maximum (value : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan prepared other
  allowance minimum → Nat) :
    List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan prepared other allowance minimum) →
      Nat
  | [] => minimum
  | head :: tail => max (value head)
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.maximum value tail)

/-- Every retained plan's selected index or depth is at most the common finite maximum. -/
theorem le_maximum (value : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan prepared other
  allowance minimum → Nat)
    {plans : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan prepared other allowance
      minimum)} {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan prepared other
      allowance minimum}
    (member : plan ∈ plans) : value plan ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.maximum value plans := by
  induction plans with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      rcases List.Membership.mem_cons.mp member with same | member
      · subst plan; exact Nat.Order.le_max_left ..
      · exact (ih member).trans (Nat.Order.le_max_right ..)

end PairedArcPlan

set_option genInjectivity false in
/-- A count-paid paired-area request over the exact original exterior occurrence list.

The local requests and their common model index and literal inverse-arc depth are retained before evaluation. -/
structure PairedArcRequest (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (other : Hyperelliptic.Differentials.Basic.Differential genus) (target : Fraction.Rational) (minimum : Nat) where
  /-- The retained local paired-area allowance. -/ allowance : Fraction.Rational
  /-- The allowance is the original aggregate allocation over the occurrence count. -/ allowance_eq : allowance =
    Rational.Budget.Aggregate.perTerm target prepared.occurrences.length
  /-- The retained local allowance is positive. -/ positive : 0 < allowance
  /-- The complete original occurrence-count-squared charge is strictly below the target. -/ paid :
    (prepared.occurrences.length : Fraction.Rational) * ((prepared.occurrences.length : Fraction.Rational) * allowance)
    < target
  /-- The actual retained paired requests in original occurrence order. -/ plans : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan prepared other allowance minimum)
  /-- The plans retain exactly the original prepared occurrence list. -/ occurrences_eq : plans.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.occurrence = prepared.occurrences
  /-- The cached common sufficient polynomial-model index. -/ index : Nat
  /-- The index is the maximum of the retained parent request indices. -/ index_eq : index =
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.maximum (fun plan => plan.parents.index)
    plans
  /-- The cached common sufficient inverse-arc depth. -/ depth : Nat
  /-- The depth is the maximum of the original total occurrence depths. -/ depth_eq : depth =
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.maximum
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.depth plans

constructive_injectivity PairedArcRequest

namespace PairedArcRequest
variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {target : Fraction.Rational} {minimum stage depth : Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}

/-- Allocate the original whole-family target and cache all occurrence requests with their common sufficient index and
depth. -/
@[expose] def build (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential) (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (target : Fraction.Rational) (positive : 0 < target) (minimum : Nat) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest prepared other target minimum := by
  let allowance := Rational.Budget.Aggregate.perTerm target prepared.occurrences.length
  have h := Rational.Budget.Aggregate.perTerm_positive positive prepared.occurrences.length
  let plans := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.build prepared other allowance
    h minimum prepared.occurrences (fun _ h => h)
  exact ⟨allowance, rfl, h, Rational.Budget.Aggregate.count_mul_perTerm_lt positive prepared.occurrences.length,
    plans, Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.build_occurrences prepared other
      allowance h minimum prepared.occurrences (fun _ h => h),
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.maximum (fun plan => plan.parents.index)
      plans, rfl,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.maximum
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.depth plans, rfl⟩

variable {request : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest prepared
  other target minimum}

/-- The actual retained parent comparison at the additional depth needed to reach the shared original arc depth. -/
@[expose] def ParentEvaluation (plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan
  prepared other request.allowance minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox) (depth : Nat) :=
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation plan.parents sample otherSample (depth -
    plan.depth)

/-- The paired polynomial endpoint chord on one original exterior occurrence. -/
@[expose] def chordValue (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox) : Gaussian :=
  Topology.Polygon.Stokes.edgeArea
    ⟨sample.primitive.value.eval occurrence.start⁻¹, otherSample.primitive.value.eval occurrence.start⁻¹⟩
    ⟨sample.primitive.value.eval occurrence.finish⁻¹, otherSample.primitive.value.eval occurrence.finish⁻¹⟩

/-- The literal paired inverse-arc area on one original exterior occurrence at the retained depth. -/
@[expose] def arcValue (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox) (depth : Nat) :
      Gaussian :=
  Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
    (fun point => ⟨sample.primitive.value.eval point, otherSample.primitive.value.eval point⟩)
    depth occurrence.start occurrence.finish

set_option genInjectivity false in
/-- One actual paired parent comparison with cached source and cap summaries and the original endpoint chord.

The depth equation binds both summaries to the common literal arc depth and the local accuracy retains the original
allowance. -/
structure Entry (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest prepared other
  target minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox) (depth : Nat) where
  /-- The original occurrence and parent request retained by this entry. -/ plan :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan prepared other request.allowance minimum
  /-- The actual paired parent evaluation at the retained shared depth. -/ compared :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.ParentEvaluation plan sample
    otherSample depth
  /-- The occurrence and parent refinement depths sum to the common literal arc depth. -/ depth_eq :
    plan.occurrence.piece.mesh.depth + (plan.parents.depth + (depth - plan.depth)) = depth
  /-- The cached summary of the original source increment paths. -/ source : Path.PairedIncrementArea.Summary
    (compared.pairs.map Prod.fst).flatten
  /-- The cached summary of the paired cap increment paths. -/ cap : Path.PairedIncrementArea.Summary
    (compared.pairs.map Prod.snd).flatten
  /-- The cached original paired endpoint chord. -/ chord : Gaussian.Basic.Canonical
  /-- The chord is exactly the polynomial endpoint value of the retained occurrence. -/ chord_eq : chord =
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.chordValue plan.occurrence sample
    otherSample
  /-- The actual source-minus-cap area meets the retained local allowance. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq (source.areaValue - cap.areaValue) < request.allowance

constructive_injectivity Entry

/-- Evaluate one retained occurrence at sufficient shared model index and arc depth, caching both summaries and its
original chord. -/
@[expose] def entry (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest prepared
  other target minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox)
    (chart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) (later : request.index ≤
      stage)
    (spatial : request.depth ≤ depth) (plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan
      prepared other request.allowance minimum) (member : plan ∈ request.plans) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Entry request sample otherSample depth
      := by
  have indexLe := (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.le_maximum (fun plan =>
    plan.parents.index) member).trans (request.index_eq ▸ later)
  have depthLe := (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.le_maximum
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.depth member).trans (request.depth_eq ▸
    spatial)
  let compared := plan.parents.evaluate sample otherSample chart indexLe (depth - plan.depth)
  let source := Path.PairedIncrementArea.Summary.build (compared.pairs.map Prod.fst).flatten
  let capSummary := Path.PairedIncrementArea.Summary.build (compared.pairs.map Prod.snd).flatten
  have accurate := plan.occurrence.paired_area_error compared
  refine ⟨plan, compared, ?_, source, capSummary,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.chordValue plan.occurrence sample
    otherSample, rfl, ?_⟩
  · rw [← Nat.add_assoc]
    exact Nat.Subtraction.add_sub_of_le depthLe
  · rw [source.area_eq, capSummary.area_eq]
    exact accurate

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest in
/-- The cached cap increment area plus its endpoint chord equals the actual inverse arc at the common depth. -/
theorem Entry.arc_eq (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Entry request
  sample otherSample depth) :
    entry.cap.areaValue + entry.chord =
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.arcValue entry.plan.occurrence sample
      otherSample depth := by
  rw [entry.cap.area_eq, Integration.PreparedPairedParentCapReadback.SurfaceOccurrence.paired_cap_area_arc
    entry.plan.occurrence entry.compared, entry.depth_eq, entry.chord_eq]
  unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.chordValue
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.arcValue
  ring1

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest
/-- Evaluate the supplied retained plans in order using the same original samples and shared depth. -/
@[expose] def entries (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest prepared
  other target minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox)
    (chart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) (later : request.index ≤
      stage) (spatial : request.depth ≤ depth) :
    (plans : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan prepared other
      request.allowance minimum)) →
    (∀ plan ∈ plans, plan ∈ request.plans) → List
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Entry request sample otherSample
      depth)
  | [], _ => []
  | plan :: tail, member => entry request sample otherSample chart later spatial plan (member plan List.mem_cons_self)
    ::
      entries request sample otherSample chart later spatial tail (fun plan retained => member plan
        (List.mem_cons_of_mem _ retained))

/-- The evaluated entries retain exactly the supplied original plan list. -/
private theorem entries_plans (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest
  prepared other target minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox)
    (chart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) (later : request.index ≤
      stage) (spatial : request.depth ≤ depth)
    (plans : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan prepared other
      request.allowance minimum))
    (member : ∀ plan ∈ plans, plan ∈ request.plans) :
    (entries request sample otherSample chart later spatial plans member).map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Entry.plan = plans := by
  induction plans with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) (ih _)

/-- The evaluated entries retain exactly the supplied original plan list. -/
theorem entries_plans_for_evaluate (request :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest prepared other target minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox)
    (chart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) (later : request.index ≤
      stage) (spatial : request.depth ≤ depth)
    (plans : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan prepared other
      request.allowance minimum))
    (member : ∀ plan ∈ plans, plan ∈ request.plans) :
    (entries request sample otherSample chart later spatial plans member).map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Entry.plan = plans := by
  induction plans with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) (ih _)

end

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest in
set_option genInjectivity false in
/-- The original ordered occurrence comparisons with a cached total discrepancy and its count-paid family accuracy. -/
structure Evaluation (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest prepared
  other target minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox) (depth : Nat) where
  /-- The actual evaluated entries in original plan order. -/ retained : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Entry request sample otherSample
    depth)
  /-- The entries retain exactly the original request's plans. -/ plans_eq : retained.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Entry.plan = request.plans
  /-- The cached total source-minus-cap discrepancy. -/ error : Gaussian.Basic.Canonical
  /-- The error equals the sum of the actual retained local discrepancies. -/ error_eq : error =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (retained.map (fun entry => entry.source.areaValue - entry.cap.areaValue))
  /-- The cached total discrepancy meets the whole-family target. -/ accurate : Data.Gaussian.Norm.Basic.normSq
    error < target

constructive_injectivity Evaluation

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest
/-- Evaluate every retained plan once and cache the sum of actual source-minus-cap discrepancies with the original paid
bound. -/
@[expose] def evaluate (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest prepared
  other target minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox)
    (chart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) (later : request.index ≤
      stage) (spatial : request.depth ≤ depth) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Evaluation request sample otherSample
      depth := by
  let retained := entries request sample otherSample chart later spatial request.plans (fun _ h => h)
  have plans := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.entries_plans_for_evaluate
    request sample otherSample chart later spatial request.plans (fun _ h => h)
  let errors := retained.map (fun entry => entry.source.areaValue - entry.cap.areaValue)
  have bound := Gaussian.Norm.Sum.Bounds.normSq_sum_le errors request.allowance (by
    intro value member
    obtain ⟨entry, _, rfl⟩ := Data.List.Map.mem_map.mp member
    exact entry.accurate.le)
  have count : retained.length = prepared.occurrences.length := by
    have h := congrArg List.length ((congrArg (List.map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.occurrence) plans).trans
      request.occurrences_eq)
    simpa only [Data.List.Map.length_map] using h
  simp only [errors, Data.List.Map.length_map, count] at bound
  exact ⟨retained, plans, Data.Gaussian.Norm.Sum.Basic.gaussianSum errors, rfl, bound.trans_lt request.paid⟩

/-- The original source-minus-cap discrepancy equals source area plus endpoint chords minus the literal inverse-arc sum.
-/
private theorem sum_readback (retained : List
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Entry request sample otherSample depth))
  :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (retained.map (fun entry => entry.source.areaValue - entry.cap.areaValue))
      =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (retained.map (fun entry => entry.source.areaValue + entry.chord)) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (retained.map (fun entry =>
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.arcValue entry.plan.occurrence
          sample otherSample depth)) := by
  induction retained with
  | nil => change (0 : Gaussian.Basic.Canonical) = 0 - 0; ring1
  | cons head tail ih =>
      change (head.source.areaValue - head.cap.areaValue) + _ =
        (head.source.areaValue + head.chord + _) -
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.arcValue head.plan.occurrence
          sample otherSample depth + _)
      rw [ih, ← head.arc_eq]
      ring1

end

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest in
/-- The original source summaries and chords approximate the literal occurrence arc sum within the retained target. -/
@[expose] def Evaluation.ArcError (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Evaluation request sample otherSample
  depth) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.retained.map (fun entry =>
    entry.source.areaValue + entry.chord)) -
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.occurrences.map (fun occurrence =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.arcValue occurrence sample
      otherSample depth))) < target

/-- The cached local summaries read back to every literal inverse arc at the
same depth. Endpoint chords remain explicit until the closed attachment is
assembled; they are not silently discarded as zero-total paths. -/
theorem Evaluation.arc_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Evaluation request sample otherSample
  depth) : evaluated.ArcError := by
  have occurrences := (congrArg (List.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.occurrence) evaluated.plans_eq).trans
    request.occurrences_eq
  have arcs := congrArg (fun occurrences => Data.Gaussian.Norm.Sum.Basic.gaussianSum (occurrences.map (fun occurrence =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.arcValue occurrence sample otherSample
    depth))) occurrences
  rw [Data.List.Map.map_map, Data.List.Map.map_map] at arcs
  change Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.retained.map (fun entry =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.arcValue entry.plan.occurrence sample
      otherSample depth)) = _ at arcs
  have bound := evaluated.accurate
  rw [evaluated.error_eq, Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.sum_readback,
    arcs] at bound
  exact bound

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest in

/-- The original occurrence arc sum equals the forward inverse-arc sum on the exact attached cap words. -/
theorem attachment_arcs (attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
  prepared)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox) (depth : Nat) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.occurrences.map (fun occurrence =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.arcValue occurrence sample
      otherSample depth)) =
      Geometry.Grid.CellBoundary.sumValues (fun word => Geometry.Grid.CellBoundary.sumValues (fun edge =>
        Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
        (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) depth
        (lifted.vertices.coordinate edge.start) (lifted.vertices.coordinate edge.finish)) word) attached.words := by
  rw [Geometry.Grid.CellBoundary.sumValues_flatten, attached.words_flatten, ← prepared.indexed_eq,
    Data.List.Map.map_map]
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  apply Data.List.Map.map_congr_left
  intro occurrence _
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.arcValue, Function.comp_def]
  rw [occurrence.placement.start_eq, occurrence.placement.finish_eq]
  rfl

variable {attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared}
  {geometry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
  attached}
  {left : Charts.Reciprocal.Cap.EnergyBounds sample} {right :
    Charts.Reciprocal.Cap.EnergyBounds otherSample}
  {capTarget : Fraction.Rational} {capFloor : Nat}
  {capRequest : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest attached left right
    capTarget capFloor}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest in
/-- The original source summaries and endpoint chords cancel the actual attached cap area within the retained target. -/
@[expose] def Evaluation.CapError
    (evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Evaluation request sample
      otherSample capRequest.localRequest.depth)
    (caps : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Evaluation capRequest
      geometry) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.retained.map (fun entry =>
    entry.source.areaValue + entry.chord)) + caps.area) < target

/-- The actual closed cap interface cancels the sum of forward inverse arcs.
Only the retained source endpoint chords remain visible in this comparison. -/
theorem Evaluation.cap_error
    (evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Evaluation request sample
      otherSample capRequest.localRequest.depth)
    (caps : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Evaluation capRequest
      geometry) : evaluated.CapError caps := by
  have bound := evaluated.arc_error
  unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Evaluation.ArcError at bound
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.attachment_arcs attached] at bound
  have opposite := eq_neg_of_add_eq_zero_left

      (PairedCapBoundary.CapAttachment.PairedFamilyRequest.Evaluation.forward_arcs_cancel
      caps)
  rw [opposite] at bound
  have cancel (a b : Gaussian.Basic.Canonical) : a - -b = a + b := by ring1
  rw [cancel] at bound
  exact bound

end PairedArcRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily
