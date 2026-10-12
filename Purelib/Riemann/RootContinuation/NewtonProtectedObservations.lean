module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Data.List.Permutation
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Riemann.Readings.ProtectedObservationRegion
public import Purelib.Riemann.Readings.ContainedObservationEnergy
public import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Polynomial.Geometry.Grid.ClearGridCoverage
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Data.Vector.Basic
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data

public section

/-!
# Positive observation boxes surviving actual Newton excision

One coefficient-independent bank is placed inside the original period
ambient before any Newton request. Every later band misses every observation
box. Point location uses the existing classified grid and returns a retained
regular face; both sheets and both triangle occurrences survive in the
actual sewn sample. This is geometric coverage and a local positive lower
sum, not yet the global period-versus-energy comparison.
-/

namespace Purelib.Riemann.RootContinuation.NewtonProtectedObservations

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Readings.ProtectedObservationRegion (ObservationRegion)
open _root_.Purelib.Riemann.Readings (ContainedObservationEnergy)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceTrace)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (Sewn)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}

open Purelib in
set_option genInjectivity false in
/-- A protected clear region and contained observation energy for the original branch bank.

The energy owner is indexed by the exact retained region box, so later Newton grids retain the same observation sites
and quantitative lower bound. -/
structure ProtectedObservations (original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher) where
  /-- The protected clear region owned by the original branch-cell bank. -/ region : ObservationRegion original
  /-- The contained observation energy on that exact retained protected box. -/ energy : ContainedObservationEnergy
    curve.polynomial region.box genus

constructive_injectivity ProtectedObservations

namespace ProtectedObservations

open Purelib in
/-- Construct the original protected region and its contained observation energy once. -/
@[expose] def build (original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher) :
  ProtectedObservations original :=
  let region := ObservationRegion.build original
  ⟨region, ContainedObservationEnergy.build region.observations⟩

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Geometry.Rational in
/-- Every original protected observation square lies strictly inside the same ambient box. -/
theorem box_interior (observations : ProtectedObservations original) (site : Fin genus) :
    (observations.energy.box site).StrictInterior (Cuts.Ambient curve) :=
  Geometry.Rational.Box.Refinement.StrictInterior.of_refines observations.region.interior
      (observations.energy.box_refines_region
    site)

open Purelib in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.LinearAlgebra.Gaussian in
/-- The protected observation energy retains its uniform coefficient-norm lower bound. -/
theorem uniform_lower (observations : ProtectedObservations original) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector
  genus)
    (face : Topology.BranchedCover.Double.Attachment.Face) : observations.energy.lower * coefficientNormSq coefficients
      ≤
      Energy.Prepared.surfaceEnergy (fun index => observations.energy.surfaceCells coefficients face index) :=
  observations.energy.uniform_lower coefficients face

variable {preparation : NewtonPreparation original} {target radius : Rational} {grid :
  NewtonGrid preparation target radius}

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
/-- Every protected observation point lies outside each original Newton band box. -/
theorem outside_band (observations : ProtectedObservations original) (site : Fin genus) {point : Basic.Canonical}
    (inside : (observations.energy.box site).Contains point) (index : BranchIsolation.Data.Index branches) :
    ¬ (grid.bands.box index).Contains point :=
  observations.region.outside_refinement index (Geometry.Rational.Box.Refinement.StrictInterior.refines
      (grid.bands.entries.get
    index).selection.sample.output.strictCurrent)
    ((observations.energy.box_refines_region site).contains inside)

open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- An original regular-face index whose cell contains the given observation point.

The bounded position indexes the exact Newton grid's retained regular list, together with its original box-containment
certificate. -/
structure RegularLocation (grid : NewtonGrid preparation target radius) (point : Basic.Canonical) where
  /-- The bounded index into the original Newton grid's retained regular-face list. -/ position : Fin
    grid.faces.regulars.length
  /-- The cell at that exact original regular index contains the specified point. -/ contains :
    grid.faces.regulars[position.val].cell.box.Contains point

constructive_injectivity RegularLocation

open Purelib in
open Purelib.Data.Gaussian in
/-- Find the first containing cell in the original finite regular-face list.

An explicit existence witness ensures the recursive search succeeds; the result retains the original list index and the
matching cell's containment proof. -/
@[expose] public def findRegular (bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher) (point :
  Basic.Canonical) :
    (faces : List (RegularFace bank)) → (∃ face ∈ faces, face.cell.box.Contains point) →
      {position : Fin faces.length // faces[position.val].cell.box.Contains point}
  | [], found => False.elim (by obtain ⟨_, member, _⟩ := found; exact List.not_mem_nil member)
  | first :: remaining, found =>
      if inside : first.cell.box.Contains point then ⟨0, inside⟩
      else
        let tail := findRegular bank point remaining (by
          obtain ⟨face, member, contains⟩ := found
          rcases List.Membership.mem_cons.mp member with rfl | member
          · exact (inside contains).elim
          · exact ⟨face, member, contains⟩)
        ⟨⟨tail.val.val + 1, Nat.succ_lt_succ tail.val.isLt⟩, tail.property⟩

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- Locate a protected observation point in the exact original Newton grid's regular list.

The frame cover gives a cell, while the protected-region certificate excludes every retained band hole; the finite
search returns an original bounded regular position. -/
@[expose] def locate (observations : ProtectedObservations original) (grid : NewtonGrid preparation target radius)
    (site : Fin genus) (point : Basic.Canonical) (inside : (observations.energy.box site).Contains point) :
      RegularLocation grid point := by
  let located := grid.shrunk.prepared.frame.locate (Bounds.RootRadius.Box.largeSquareBox_proper curve.polynomial) point
    ((Geometry.Rational.Box.Refinement.StrictInterior.refines (observations.box_interior site)).contains inside)
  have found : ∃ face ∈ grid.faces.regulars, face.cell.box.Contains point := by
    rcases grid.faces.split.covers located.member with ⟨face, member, equal⟩ | ⟨hole, _, equal⟩
    · refine ⟨face, grid.faces.regulars_eq.symm ▸ member, ?_⟩
      rw [equal]
      exact located.contains
    · have inHole : hole.cell.box.Contains point := equal.symm ▸ located.contains
      exact (observations.outside_band site inside hole.index ((grid.hole_refines_band hole).contains inHole)).elim
  let result := findRegular grid.shrunk.prepared.toBranchCellBank point grid.faces.regulars found
  exact ⟨result.val, result.property⟩

open Purelib.Topology.Surface in
/-- Find the first retained face trace with the specified original source index.

The supplied membership witness refers to the same ordered entry list, and the result retains both entry membership and
exact source equality. -/
@[expose] public def findTrace {faceCount count : Nat} {localValues : Fin faceCount →
  Sewing.PrimitiveSewing.PrimitiveValues 3} {values : Sewing.PrimitiveSewing.PrimitiveValues count}
    (source : Fin faceCount) : (entries : List (Sewing.SewnPrimitiveFaces.FaceTrace localValues values)) →
      source ∈ entries.map Sewing.SewnPrimitiveFaces.FaceTrace.source → {trace : Sewing.SewnPrimitiveFaces.FaceTrace
        localValues values // trace ∈ entries ∧ trace.source = source}
  | [], member => (List.not_mem_nil member).elim
  | first :: remaining, member =>
      if equal : first.source = source then ⟨first, List.mem_cons_self, equal⟩
      else
        let tail := findTrace source remaining (by
          rcases List.Membership.mem_cons.mp member with same | member
          · exact (equal same.symm).elim
          · exact member)
        ⟨tail.val, List.mem_cons_of_mem _ tail.property.1, tail.property.2⟩

variable {lifted : LiftedPuncturedGrid grid.punctured}
  {localValues : Fin lifted.mesh.triangles.length → PrimitiveValues 3}
  {sample : CachedSample lifted.cutPolygon.patch localValues}
  {excision : AllHoleExcision grid lifted}

open Purelib.Data.Gaussian in
open Purelib.Riemann.Topology in
open Purelib.Topology.Surface in
set_option genInjectivity false in
/-- An original sewn face trace retained for one protected regular triangle.

The trace keeps the exact local and sewn primitive values, the original regular position, sheet and triangle half, and
its membership in the retained sewn remainder. -/
structure RetainedTriangle (sewn : NewtonSewnExcision.AllHoleExcision.Sewn excision sample)
    {point : Basic.Canonical} (location : RegularLocation grid point) (sheet : Fin 2) (upper : Bool) where
  /-- The original face trace with the exact local and retained sewn primitive values. -/ trace :
    Sewing.SewnPrimitiveFaces.FaceTrace localValues sample.sewn.values
  /-- The trace source is the original triangle index at this regular position, sheet and half. -/ source_eq :
    trace.source = lifted.mesh.triangleIndex location.position sheet upper
  /-- The same original trace belongs to the sewn remainder's retained trace list. -/ retained : trace ∈
    sewn.remaining.traces

constructive_injectivity RetainedTriangle

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Riemann.Topology in
/-- Recover the exact sewn triangle trace at a protected regular location.

The original source coverage supplies the trace, and exclusion from all original Newton bands certifies that this same
trace survives in the sewn remainder. -/
@[expose] def retainedTriangle (observations : ProtectedObservations original)
    (sewn : NewtonSewnExcision.AllHoleExcision.Sewn excision sample) (site : Fin genus) (point : Basic.Canonical)
    (inside : (observations.energy.box site).Contains point) (location : RegularLocation grid point)
    (sheet : Fin 2) (upper : Bool) : RetainedTriangle sewn location sheet upper := by
  let source := lifted.mesh.triangleIndex location.position sheet upper
  have member : source ∈ sample.faces.entries.map FaceTrace.source := by
    rw [sample.faces.sources_eq]
    exact (Permutation.mem_iff lifted.cutPolygon.coverage source).mpr
      (Permutation.ofFn_mem _ source)
  let found := findTrace source sample.faces.entries member
  refine ⟨found.val, found.property.2, sewn.trace_survives found.val found.property.1 point ?_
    (fun index => observations.outside_band site inside index)⟩
  rw [found.property.2]
  exact Eq.mpr (congrArg (fun position : Fin grid.faces.regulars.length =>
    grid.faces.regulars[position.val].cell.box.Contains point)
      (NewtonSewnExcision.AllHoleExcision.sourcePosition_triangleIndex lifted location.position sheet upper))
        location.contains

end ProtectedObservations
end Purelib.Riemann.RootContinuation.NewtonProtectedObservations
