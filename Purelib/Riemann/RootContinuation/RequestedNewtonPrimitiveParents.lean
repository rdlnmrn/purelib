module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedIncrements
public import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.UniformPreparedBoundarySegments
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParent
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveIncrementArea
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveAreaReadback
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Integration.PreparedPairedModelAccuracy
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedVertices
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Topology.Polygon.Stokes
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedModelAccuracy
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Requested parent banks retain individual indices and cached area errors. -/
section

open Purelib
open Purelib.Data.Rat
open Purelib.RootIsolation.Newton.Band
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParent (RequestedPrimitiveParent)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank (PairedBoundaryParents)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.NewtonBandBounds (PairedParentPrimitives)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary)

namespace Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- A cached original primitive-minus-numerical area with its quantitative bound.

The stored value retains an exact signed readback and squared-norm payment against the supplied target. -/
structure PrimitiveAreaCharge (primitive numerical : Basic.Canonical) (target : Fraction.Rational) where
  /-- The cached original signed primitive-minus-numerical area difference. -/ value : Basic.Canonical
  /-- The stored value is exactly the specified original signed difference. -/ value_eq : value = primitive - numerical
  /-- The cached difference satisfies the retained squared-norm target. -/ bounded : Data.Gaussian.Norm.Basic.normSq
    value ≤
    target

constructive_injectivity PrimitiveAreaCharge

end Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target} {areaTarget :
    Purelib.Data.Rat.Fraction.Rational}

namespace Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParent.RequestedPrimitiveParent

open Purelib.Integration.Path in
open Purelib.Riemann.RootContinuation in
/-- The area-charge type indexed by an original requested primitive parent's two actual increment lists. -/
@[expose] def AreaCharge
  {parent : CenteredEdge curve differential}
    (prepared : RequestedPrimitiveParent request parent other count areaTarget) :=
    Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents.PrimitiveAreaCharge
      (PairedIncrementArea.area ((prepared.1.primitiveIncrementPairs prepared.2.2.1 prepared.2.2.2.val).map Prod.fst))
      (PairedIncrementArea.area (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments prepared.1)) areaTarget

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Riemann.RootContinuation in
/-- Cache the original parent's signed area difference with its retained paid comparison. -/
@[expose] def charge
  {parent : CenteredEdge curve differential}
    (prepared : RequestedPrimitiveParent request parent other count areaTarget) : prepared.AreaCharge :=
  ⟨_, rfl, Eq.mpr (congrArg₂ (fun primitive numerical => Data.Gaussian.Norm.Basic.normSq (primitive - numerical) ≤
    areaTarget)
    (prepared.1.primitiveIncrementPairs_area prepared.2.2.1 prepared.2.2.2.val)
    (PairedIncrementArea.area_eq_trace (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments prepared.1)))
      prepared.2.2.2.property.1⟩

end Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParent.RequestedPrimitiveParent

namespace Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Original requested primitive parents with separately retained area charges.

The exact parent list indexes the ordered bank; every head stores its own comparison and actual cached charge before the
tail. -/
inductive RequestedPrimitiveParents (request : PreparedBandRequest fixed target) (other :
  Differentials.Basic.Differential genus)
    (count : Nat) (areaTarget : Fraction.Rational) : List (CenteredEdge curve differential) → Type 2
  /-- The requested family for the exact empty original parent list. -/ | nil : RequestedPrimitiveParents request other
    count areaTarget []
  /-- Prepend an original requested parent, its actual cached charge and retained tail. -/ | cons {parent : CenteredEdge
    curve differential} {parents : List (CenteredEdge curve differential)}
      (head : RequestedPrimitiveParent request parent other count areaTarget)
      (charge : head.AreaCharge)
      (tail : RequestedPrimitiveParents request other count areaTarget parents) :
      RequestedPrimitiveParents request other count areaTarget (parent :: parents)

constructive_injectivity RequestedPrimitiveParents

end Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents

end

section

open Purelib
open Purelib.Data.Rat
open Purelib.RootIsolation.Newton.Band
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParent (RequestedPrimitiveParent)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank (PairedBoundaryParents)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.NewtonBandBounds (PairedParentPrimitives)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target} {areaTarget :
    Purelib.Data.Rat.Fraction.Rational}

section

namespace Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents.RequestedPrimitiveParents

/-- Prepend an original requested parent with its actual computed area charge. -/
@[expose] def prepend {parent : CenteredEdge curve differential}
    {parents : List (CenteredEdge curve differential)}
    (head : RequestedPrimitiveParent request parent other count areaTarget)
    (tail : RequestedPrimitiveParents request other count areaTarget parents) :
    RequestedPrimitiveParents request other count areaTarget (parent :: parents) :=
  .cons head head.charge tail

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
/-- Prepare the original covered parent list with one shared local area target.

The retained coverage, boundary memberships and properness witnesses feed each exact parent construction in list order.
-/
@[expose] def build (request : PreparedBandRequest fixed target) (other : Differentials.Basic.Differential genus)
    (otherProfile : DifferentialProfile profile other.exponent) (count : Nat)
    (areaTarget : Fraction.Rational) (positive : 0 < areaTarget) :
    {parents : List (CenteredEdge curve differential)} → Observation.UniformPreparedMesh.CoveredParents count parents →
    (∀ parent ∈ parents, ParentOnBoundary parent request.sample.output.box) →
    PreparedDyadicRefinements.AllParentsProper parents →
      RequestedPrimitiveParents request other count areaTarget parents
  | _, .nil, _, _ => .nil
  | _, .cons (parent := parent) patch finishInside tail, boundary, proper =>
    let head := RequestedPrimitiveParent.build request parent other otherProfile
      (boundary parent (List.mem_cons_self ..)) patch count finishInside proper.1 areaTarget positive
    prepend head (build request other
      otherProfile count areaTarget positive tail
      (fun parent member => boundary parent (List.mem_cons_of_mem _ member)) proper.2)

/-- Prepend the actual paired refinement of an original requested parent. -/
@[expose] def prependBank {parent : CenteredEdge curve differential}
    {parents : List (CenteredEdge curve differential)}
    (head : RequestedPrimitiveParent request parent other count areaTarget)
    (tail : PairedBoundaryParents request other parents) :
    PairedBoundaryParents request other (parent :: parents) := .cons head.1 tail

/-- Read the exact original paired-parent bank from the retained requested family. -/
@[expose] def bank : {parents : List (CenteredEdge curve differential)} →
    RequestedPrimitiveParents request other count areaTarget parents → PairedBoundaryParents request other parents
  | _, .nil => .nil
  | _, .cons head _ tail =>
    prependBank head tail.bank

/-- Prepend both stored original primitive comparisons to their exact dependent bank. -/
@[expose] def prependPrimitives {parent : CenteredEdge curve differential}
    {parents : List (CenteredEdge curve differential)}
    (head : RequestedPrimitiveParent request parent other count areaTarget)
    {tail : PairedBoundaryParents request other parents}
    (rest : PairedParentPrimitives count tail) :
    PairedParentPrimitives count (prependBank head tail) :=
  .cons head.2.2.1 head.2.2.2.val rest

/-- Read the original paired primitive comparisons indexed by the retained bank. -/
@[expose] def primitives : {parents : List (CenteredEdge curve differential)} →
    (prepared : RequestedPrimitiveParents request other count areaTarget parents) → PairedParentPrimitives count
      prepared.bank
  | _, .nil => .nil
  | _, .cons head _ tail =>
    prependPrimitives head
    tail.primitives

end Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents.RequestedPrimitiveParents

section
open Purelib.Data.Gaussian

namespace Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents.RequestedPrimitiveParents

/-- Prepend the actual cached signed area-charge value. -/
@[expose] def prependError {parent : CenteredEdge curve differential}
    (head : RequestedPrimitiveParent request parent other count areaTarget)
    (charge : head.AreaCharge) (tail : List Basic.Canonical) :
    List Basic.Canonical := charge.value :: tail

/-- Read original cached internal area errors in retained parent order. -/
@[expose] def internalErrors : {parents : List (CenteredEdge curve differential)} →
    RequestedPrimitiveParents request other count areaTarget parents → List Basic.Canonical
  | _, .nil => []
  | _, .cons head charge tail =>
    prependError head charge
    tail.internalErrors

end Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents.RequestedPrimitiveParents

end

namespace Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents.RequestedPrimitiveParents

/-- There is exactly one retained internal error per original parent. -/
theorem internalErrors_length {parents : List (CenteredEdge curve differential)}
    (prepared : RequestedPrimitiveParents request other count areaTarget parents) :
    prepared.internalErrors.length = parents.length := by
  induction prepared with
  | nil => rfl
  | cons head charge tail ih => exact congrArg Nat.succ ih

end Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents.RequestedPrimitiveParents

section
open Purelib.Data.Gaussian

namespace Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents.RequestedPrimitiveParents

/-- Every original internal error satisfies the shared retained local target. -/
theorem internalErrors_bounded {parents : List (CenteredEdge curve differential)}
    (prepared : RequestedPrimitiveParents request other count areaTarget parents) :
    ∀ error ∈ prepared.internalErrors, Data.Gaussian.Norm.Basic.normSq error ≤ areaTarget := by
  induction prepared with
  | nil => intro error member; cases member
  | cons head charge tail ih =>
    intro error member
    rcases Data.List.Membership.mem_cons.mp member with rfl | member
    · exact charge.bounded
    · exact ih error member

/-- Adding two signed scalar errors equals the difference of their original summed values. -/
private theorem sum_error_step (p n rp rn : Basic.Canonical) :
    (p - n) + (rp - rn) = (p + rp) - (n + rn) := by ring1

end Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents.RequestedPrimitiveParents

end

namespace Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents.RequestedPrimitiveParents

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Riemann.RootContinuation in
/-- The cached original errors sum to primitive internal areas minus numerical internal areas. -/
theorem internalErrors_sum {parents : List (CenteredEdge curve differential)}
    (prepared : RequestedPrimitiveParents request other count areaTarget parents) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum prepared.internalErrors =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.primitives.primitiveBlocks.map PairedIncrementArea.area) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.bank.incrementBlocks.map PairedIncrementArea.area) := by
  induction prepared with
  | nil => change (0 : Basic.Canonical) = 0 - 0; ring1
  | cons head charge tail ih =>
    change charge.value + Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.internalErrors =
      (PairedIncrementArea.area ((head.1.primitiveIncrementPairs head.2.2.1 head.2.2.2.val).map Prod.fst) +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.primitives.primitiveBlocks.map PairedIncrementArea.area)) -
      (PairedIncrementArea.area (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments head.1) +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.bank.incrementBlocks.map PairedIncrementArea.area))
    exact (congrArg₂ (fun a b : Basic.Canonical => a + b) charge.value_eq ih).trans
      (sum_error_step _ _ _ _)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Bound the original internal-area discrepancy by parent count squared times the local target. -/
theorem internal_area_error_le {parents : List (CenteredEdge curve differential)}
    (prepared : RequestedPrimitiveParents request other count areaTarget parents) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.primitives.primitiveBlocks.map
      PairedIncrementArea.area) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.bank.incrementBlocks.map PairedIncrementArea.area)) ≤
        (parents.length : Fraction.Rational) * ((parents.length : Fraction.Rational) * areaTarget) := by
  rw [← prepared.internalErrors_sum]
  have bounded := Norm.Sum.Bounds.normSq_sum_le prepared.internalErrors areaTarget prepared.internalErrors_bounded
  rwa [prepared.internalErrors_length] at bounded

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- A retained local target and original requested bank paying a specified total internal-area error.

The exact parent list and actual primitive/numerical block-area sums remain indices of the guarantee. -/
@[expose] def InternalAreaRequest (request : PreparedBandRequest fixed target) (other : Differentials.Basic.Differential
  genus)
    (count : Nat) (parents : List (CenteredEdge curve differential)) (areaTarget : Fraction.Rational) :=
  (localTarget : Fraction.Rational) ×
    { prepared : RequestedPrimitiveParents request other count localTarget parents //
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.primitives.primitiveBlocks.map
        PairedIncrementArea.area) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.bank.incrementBlocks.map PairedIncrementArea.area)) ≤
          areaTarget }

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
/-- Allocate and prepare original parent comparisons to pay the requested total internal area.

The per-term allowance uses the exact retained parent count; original coverage, boundary and properness witnesses
determine the resulting bank. -/
@[expose] def acquire (request : PreparedBandRequest fixed target) (other : Differentials.Basic.Differential genus)
    (otherProfile : DifferentialProfile profile other.exponent) (count : Nat)
    {parents : List (CenteredEdge curve differential)} (covered : Observation.UniformPreparedMesh.CoveredParents count
      parents)
    (boundary : ∀ parent ∈ parents, ParentOnBoundary parent request.sample.output.box)
    (proper : PreparedDyadicRefinements.AllParentsProper parents)
    (areaTarget : Fraction.Rational) (positive : 0 < areaTarget) :
    InternalAreaRequest request other count parents areaTarget := by
  let localTarget := Budget.Aggregate.perTerm areaTarget parents.length
  let prepared := build request other otherProfile count localTarget
    (Budget.Aggregate.perTerm_positive positive parents.length) covered boundary proper
  exact ⟨localTarget, prepared, prepared.internal_area_error_le.trans
    (Budget.Aggregate.count_mul_perTerm_lt positive parents.length).le⟩

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Meshes in
open Purelib.Riemann.Paths in
/-- Acquire the original covered side's internal-area request from its retained boundary evidence.

The same covered parents, endpoint owner and sheet supply the properness and boundary proofs; no replacement coverage is
introduced. -/
@[expose] def ofCovered (request : PreparedBandRequest fixed target) (other : Differentials.Basic.Differential genus)
    (otherProfile : DifferentialProfile profile other.exponent)
    {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial request.sample.output.box start finish}
    {within : segment.WithinAmbient}
    {owner : Observation.UniformPreparedMesh.Owner (curve.polynomial.eval (segment.pointAt
      UniformPrimitiveMesh.firstEndpoint.parameter))}
    {sheet : Fin 2} (covered : Observation.UniformPreparedMesh.CoveredSegment segment within owner differential sheet
      count)
    (side : PreparedBoundarySegments.SameSide request.sample.output.box start finish)
    (areaTarget : Fraction.Rational) (positive : 0 < areaTarget) :
    InternalAreaRequest request other count covered.parents areaTarget :=
  acquire request other otherProfile count covered.covered
    (fun _ member => UniformPreparedBoundarySegments.CoveredSegment.parent_boundary
      covered side member) covered.parents_proper areaTarget positive

end Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents.RequestedPrimitiveParents

end
end
