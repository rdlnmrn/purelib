module
import Purelib.Data.List.Membership
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.UniformPreparedBoundarySegments
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Orientation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.AngularRequest
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

/-!
# Angular orientation inherited by the actual exterior parents

The proof follows the original prepared path and uses its certified source
endpoints and positive parameter widths. It applies to the cached period
parents, including the second lap in odd degree.
-/

namespace Purelib.Polynomial.Geometry.ClearPath
public section
open Purelib
open Purelib.Curves
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration.Energy
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Integration
open Purelib.Data.List

open Purelib.Integration.Energy.AffineTriangle (crossEnergy)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

/-- Every original clear-path segment has strictly positive angular cross energy. -/
@[expose]
def PositiveAngular {polynomial : ClearPath.GaussianPolynomial} {ambient : Rational.Box} :
    {first last : Data.Gaussian.Basic.Canonical} → ClearPath polynomial ambient first last → Prop
  | _, _, .nil _ => True
  | first, _, .cons (middle := middle) _ tail => 0 < AffineTriangle.crossEnergy first middle ∧
    PositiveAngular tail

end
end Purelib.Polynomial.Geometry.ClearPath

namespace Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels
public section
open Purelib
open Purelib.Curves
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration.Energy
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Integration
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.UniformPreparedBoundarySegments (centeredEdges_source_endpoints)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Integration.Energy.AffineTriangle (crossEnergy)

/-- Two source parameters scale the original segment's angular cross energy by their ordered parameter difference. -/
private theorem source_area {polynomial : ClearPath.GaussianPolynomial} {ambient : Rational.Box}
    {first last : Data.Gaussian.Basic.Canonical} (segment : ClearPath.ClearSegment polynomial ambient first last) (left
      right : Fraction.Rational) :
    AffineTriangle.crossEnergy (segment.pointAt left) (segment.pointAt right) = (right - left) *
      AffineTriangle.crossEnergy first last := by
  simp only [AffineTriangle.crossEnergy, ClearSegment.pointAt, Data.Gaussian.Basic.conj,
    Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
    Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
    Data.Gaussian.Basic.mul_im, Data.Gaussian.Scale.scale_re, Data.Gaussian.Scale.scale_im,
    Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- Every proper actual parent inherited from a positively oriented prepared path has positive endpoint angular energy.

The proof follows membership in the retained list through its original head, tail or concatenation, preserving the
supplied occurrence witness. -/
private theorem prepared_parent_oriented (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential :
  Differentials.Basic.Differential genus)
    (sheet : Fin 2) {ambient : Rational.Box} :
    ∀ {first last : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient first
      last}
      {owner : Owner (curve.polynomial.eval first)} (prepared : PreparedPath path owner), path.PositiveAngular →
      (parent : CenteredEdge curve differential) → parent ∈ (CenteredPathChain.ofPreparedPath curve differential sheet
        prepared).parents →
      parent.edge.left.parameter < parent.edge.request.endpoint.parameter →
      0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1)
  | _, _, _, _, .nil _ _, _, _, member, _ => by cases member
  | _, _, _, _, .cons head tail owner within first rest, oriented, parent, member, proper => by
      change parent ∈ (CenteredPathChain.dataOfCompleteSegment curve differential sheet first).parents ++
        (CenteredPathChain.ofPreparedPath curve differential sheet rest).parents at member
      rcases Membership.mem_append.mp member with member | member
      · rw [CenteredPathChain.dataOfCompleteSegment_parents] at member
        have endpoints := centeredEdges_source_endpoints sheet first.subdivision
          (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve differential sheet first.subdivision) parent
            member
        rw [endpoints.1, endpoints.2, source_area]
        exact Fraction.Order.Arithmetic.mul_pos_direct (Fraction.Order.Arithmetic.sub_pos_direct proper) oriented.1
      · exact prepared_parent_oriented curve differential sheet rest oriented.2 parent member proper

/-- Each actual member of a retained proper parent list has strictly ordered endpoint parameters.

The proof follows membership in the retained list through its original head, tail or concatenation, preserving the
supplied occurrence witness. -/
theorem proper_member {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    {parents : List (CenteredEdge curve differential)} (proper : AllParentsProper parents)
    (parent : CenteredEdge curve differential) (member : parent ∈ parents) :
    parent.edge.left.parameter < parent.edge.request.endpoint.parameter := by
  induction parents with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      rcases Membership.mem_cons.mp member with same | member
      · subst parent; exact proper.1
      · exact ih proper.2 member

namespace ParentCache

/-- Every retained parent of a positively angular clear path has positive angular endpoint energy. -/
theorem oriented {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    {ambient : Rational.Box} {first last : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
      curve.polynomial ambient first last}
    {owner : Owner (curve.polynomial.eval first)} {prepared : CoveredTracedPath path owner} {sheet : Fin 2}
    (cache : ParentCache prepared differential sheet) (oriented : path.PositiveAngular)
    (parent : CenteredEdge curve differential) (member : parent ∈ cache.parents) :
    0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1) := by
  have proper := proper_member cache.proper parent member
  rw [cache.parents_eq] at member
  exact prepared_parent_oriented curve differential sheet prepared.traced.prepared oriented parent member proper

end ParentCache

end
end Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels

namespace Purelib.Polynomial.Geometry.Grid.Walks.Walk
public section
open Purelib
open Purelib.Curves
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration.Energy
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Integration
open Purelib.Data.List

open Purelib.Integration.Energy.AffineTriangle (crossEnergy coordinateTriangleArea)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Geometry.Rational (Box)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)

/-- Angular cross energy equals the coordinate triangle area based at zero. -/
private theorem origin_area (first last : Data.Gaussian.Basic.Canonical) : AffineTriangle.crossEnergy first last =
  AffineTriangle.coordinateTriangleArea 0 first last := by
  simp only [AffineTriangle.crossEnergy, AffineTriangle.coordinateTriangleArea, Data.Gaussian.Basic.conj,
    Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.zero_re,
    Data.Gaussian.Basic.zero_im, Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- Positive origin area on every original grid-walk edge gives positive angular orientation of its clear path. -/
theorem positiveAngular {polynomial : ClearPath.GaussianPolynomial} {ambient : Rational.Box} {grid :
  ClearGrid polynomial ambient} :
    {first last : Data.Gaussian.Basic.Canonical} → (walk : Walks.Walk grid first last) →
    walk.Edgewise (fun first last => 0 < AffineTriangle.coordinateTriangleArea 0 first last) → walk.path.PositiveAngular
  | _, _, .nil _, _ => trivial
  | _, _, .cons _ tail, oriented => ⟨(Polynomial.Geometry.Grid.Walks.Walk.origin_area _ _).trans_gt oriented.1,
    positiveAngular tail oriented.2⟩

end
end Purelib.Polynomial.Geometry.Grid.Walks.Walk

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram
public section
open Purelib
open Purelib.Curves
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration.Energy
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Integration
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Integration.Energy.AffineTriangle (crossEnergy)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}

/-- Every actual cached exterior-period parent retains strictly ordered endpoint parameters. -/
theorem parents_proper (program : PeriodPrograms.ExteriorProgram lifted differential)
    (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (member : parent ∈ program.cache.parents) :
    parent.edge.left.parameter < parent.edge.request.endpoint.parameter :=
  Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.proper_member program.cache.proper parent member

/-- Every actual cached exterior-period parent inherits positive angular endpoint energy from the original full exterior
walk. -/
theorem parents_oriented (program : PeriodPrograms.ExteriorProgram lifted differential)
    (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (member : parent ∈ program.cache.parents) :
    0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1) :=
  program.cache.oriented (program.period.closed.walk.positiveAngular program.walk_oriented) parent member

end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram
