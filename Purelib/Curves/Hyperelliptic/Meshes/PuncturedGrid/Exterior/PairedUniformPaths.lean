module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

open Purelib

@[expose] public section

/-! Common-depth regular polynomial paths on the two retained differential
banks have the same original parameterized geometry. These are unsigned
polynomial paths; root-sign and approximation comparisons remain separate. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

/-- Both polynomial components are sampled on each retained parent, at the
same parameter vertices. No zip can silently discard unmatched increments. -/
def pairedUniformPaths (left right : Normalization.InverseRootPolynomial.Polynomial) (depth : Nat) :
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} → {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} →
    Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers → List (List
      Topology.Polygon.Stokes.PrimitivePoint)
  | [], _, .nil => []
  | parent :: _, _, .cons _ tail =>
      Path.Dyadic.DyadicPairedPrimitivePaths.increments (fun parameter =>
        ⟨left.eval ((parent.edge.point parameter)⁻¹), right.eval ((parent.edge.point parameter)⁻¹)⟩) depth 0 1 ::
        tail.pairedUniformPaths left right depth

/-- The left projection of the complete paired uniform paths is the original left polynomial path bank. -/
theorem pairedUniformPaths_left (left right : Normalization.InverseRootPolynomial.Polynomial) (depth : Nat)
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers) :
    (bank.pairedUniformPaths left right depth).map (List.map Topology.Polygon.Stokes.PrimitivePoint.left) =
      Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniformPrimitivePaths left depth bank := by
  induction bank with
  | nil => rfl
  | cons head tail ih =>
      change List.map Topology.Polygon.Stokes.PrimitivePoint.left
        (Path.Dyadic.DyadicPairedPrimitivePaths.increments _ depth 0 1) :: _ = _
      rw [Path.Dyadic.DyadicPairedPrimitivePaths.increments_left, ih]
      rfl

/-- The right projection of the complete paired uniform paths is the original right polynomial path bank. -/
theorem pairedUniformPaths_right (left right : Normalization.InverseRootPolynomial.Polynomial) (depth : Nat)
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers) :
    (bank.pairedUniformPaths left right depth).map (List.map Topology.Polygon.Stokes.PrimitivePoint.right) =
      Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniformPrimitivePaths right depth bank := by
  induction bank with
  | nil => rfl
  | cons head tail ih =>
      change List.map Topology.Polygon.Stokes.PrimitivePoint.right
        (Path.Dyadic.DyadicPairedPrimitivePaths.increments _ depth 0 1) :: _ = _
      rw [Path.Dyadic.DyadicPairedPrimitivePaths.increments_right, ih]
      rfl

/-- Every parent contributes its actual dyadic boundary minus its endpoint
chord. The polygon joining parent totals is retained by `area_flatten`. -/
theorem pairedUniformPaths_areas (left right : Normalization.InverseRootPolynomial.Polynomial) (depth : Nat)
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers) :
    (bank.pairedUniformPaths left right depth).map Path.PairedIncrementArea.area =
      parents.map (fun parent =>
        let values := fun parameter => (⟨left.eval ((parent.edge.point parameter)⁻¹),
          right.eval ((parent.edge.point parameter)⁻¹)⟩ : Topology.Polygon.Stokes.PrimitivePoint)
        Periods.DyadicBilinearBoundaryRibbon.dyadicArea values depth 0 1 -
          Topology.Polygon.Stokes.edgeArea (values 0) (values 1)) := by
  induction bank with
  | nil => rfl
  | cons head tail ih =>
      change Path.PairedIncrementArea.area (Path.Dyadic.DyadicPairedPrimitivePaths.increments _ depth 0 1) :: _ = _
      rw [Path.Dyadic.DyadicPairedPrimitivePaths.increments_area, ih]
      rfl

/-- The complete paired uniform path area is the sum of original parent areas and the polygon of their retained totals.

Every parent contributes its dyadic boundary area minus its endpoint chord at the common explicit depth. -/
theorem pairedUniformPaths_area (left right : Normalization.InverseRootPolynomial.Polynomial) (depth : Nat)
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers) :
    Path.PairedIncrementArea.area (bank.pairedUniformPaths left right depth).flatten =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (parents.map (fun parent =>
        let values := fun parameter => (⟨left.eval ((parent.edge.point parameter)⁻¹),
          right.eval ((parent.edge.point parameter)⁻¹)⟩ : Topology.Polygon.Stokes.PrimitivePoint)
        Periods.DyadicBilinearBoundaryRibbon.dyadicArea values depth 0 1 -
          Topology.Polygon.Stokes.edgeArea (values 0) (values 1))) +
      Path.PairedIncrementArea.area ((bank.pairedUniformPaths left right depth).map Path.PairedIncrementArea.total) :=
        by
  rw [Path.PairedAreaBlocks.area_flatten, bank.pairedUniformPaths_areas]

/-- Recasting preserves every original parent path. Covers can have different
internal depths; the explicit common depth fixes the sampled vertices. -/
theorem uniformPrimitivePaths_recast (target : Hyperelliptic.Differentials.Basic.Differential genus) (value :
  Normalization.InverseRootPolynomial.Polynomial) (depth : Nat)
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
    (first : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers) :
    ∀ {otherCovers : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers (parents.map
      (Integration.PreparedEdgeRecasting.recastCenteredEdge target))}
      (last : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular otherCovers),
      Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniformPrimitivePaths value depth last =
        Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniformPrimitivePaths value depth first := by
  induction first with
  | nil => intro otherCovers last; cases last; rfl
  | cons head tail ih =>
      intro otherCovers last
      cases last with
      | cons otherHead otherTail =>
          exact congrArg (List.cons
            (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Preparation.uniformPrimitivePath head value depth)) (ih
            otherTail)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfaceOccurrence

open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceOccurrence)
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

/-- The second differential's polynomial may be evaluated on the original
bank's exact parent paths, with no endpoint-chord replacement. -/
theorem paired_uniform_paths (prepared :
  AllSurfacePreparation
  regular domains differential)
    (occurrence :
      ExteriorProgram.SurfaceOccurrence
      regular domains differential) (member : occurrence ∈ prepared.occurrences)
    (target : Hyperelliptic.Differentials.Basic.Differential genus) (value :
      Normalization.InverseRootPolynomial.Polynomial) (depth : Nat) :
    Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniformPrimitivePaths value depth
      (occurrence.pairedCap prepared member target).path.bank =
      Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniformPrimitivePaths value depth
        occurrence.cap.path.bank :=
  occurrence.cap.path.bank.uniformPrimitivePaths_recast target value depth
    (occurrence.pairedCap prepared member target).path.bank

/-- The paired path's second component is the actual recast cap path; the
first component is read from the original occurrence by `pairedUniformPaths_left`. -/
theorem paired_uniform_right (prepared :
  AllSurfacePreparation
  regular domains differential)
    (occurrence :
      ExteriorProgram.SurfaceOccurrence
      regular domains differential) (member : occurrence ∈ prepared.occurrences)
    (target : Hyperelliptic.Differentials.Basic.Differential genus) (left right :
      Normalization.InverseRootPolynomial.Polynomial) (depth : Nat) :
    (occurrence.cap.path.bank.pairedUniformPaths left right depth).map
        (List.map Topology.Polygon.Stokes.PrimitivePoint.right) =
      Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniformPrimitivePaths right depth
        (occurrence.pairedCap prepared member target).path.bank :=
  (occurrence.cap.path.bank.pairedUniformPaths_right left right depth).trans
    (occurrence.paired_uniform_paths prepared member target right depth).symm

/-- Read the requested uniform replacement's actual cached path back on the
first occurrence's parent geometry. The full regular cap area stays explicit. -/
theorem paired_uniform_area_error (prepared :
  AllSurfacePreparation
  regular domains differential)
    (occurrence :
      ExteriorProgram.SurfaceOccurrence
      regular domains differential) (member : occurrence ∈ prepared.occurrences)
    {target : Hyperelliptic.Differentials.Basic.Differential genus} {stage fine common readingIndex minimum floor : Nat}
      {box : Rational.Box}
    {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap target stage box}
    {error totalTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate}
    {capRequest : Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest.RegularRequest
      (occurrence.pairedCap prepared member target).path totalTarget areaTarget floor}
    {original : Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest.RegularRequest.Evaluation capRequest sample fine
      readingIndex}
    {request : Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Path.UniformAreaRequest
      (occurrence.pairedCap prepared member target).path sample error minimum}
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Path.UniformAreaRequest.Evaluation request original
      common) :
    Data.Gaussian.Norm.Basic.normSq
      (Path.IncrementArea.pathArea (Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.SideBank.uniformPrimitivePaths
        sample.primitive.value common occurrence.cap.path.bank).flatten -
        original.cap.area) < error := by
  have paths := evaluated.paths_eq.trans (occurrence.paired_uniform_paths prepared member target sample.primitive.value
    common)
  have area := evaluated.summary.area_eq.trans (congrArg Path.IncrementArea.pathArea
    (evaluated.path_eq.trans (congrArg List.flatten paths)))
  exact (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq (value - original.cap.area)) area).symm.trans_lt
    evaluated.area_error

end SurfaceOccurrence
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
