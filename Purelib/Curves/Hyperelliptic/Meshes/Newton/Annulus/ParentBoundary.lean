module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Riemann.Paths.PreparedPathBoundaryGeometry
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Riemann

@[expose] public section

/-! Boundary certificates for the original parents of the actual annular
excision comparison. The retained cache equality transports membership only;
no centered preparation or root continuation is rerun. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison

open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)

open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : NewtonPreparation original} {target radius : Fraction.Rational}
  {grid : NewtonGrid preparation target radius} {index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {annulus : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index} {lifted : LiftedPuncturedGrid
    grid.punctured}

section Lifted.OuterPreparation.Comparison

variable {region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted} {prepared :
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region}
  {differential : Fin genus} {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    grid.faces.regulars}
  {tolerance : Fraction.Rational}

/-- Each retained original comparison parent lies on the actual Newton band boundary.

Membership is transported through the original cache equality without repeating path preparation. -/
theorem
  parents_onBoundary
    (comparison : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison prepared
      differential domains tolerance)
    {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve (standardDifferential differential)}
    (member : parent ∈ comparison.parents.parents) :
    ParentOnBoundary parent (grid.bands.box index) := by
  rw [← comparison.parents_eq] at member
  exact Paths.PreparedPathBoundaryGeometry.onPathBoundary comparison.caches
    (Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.doubleBoundary_segments annulus) parent member

end Lifted.OuterPreparation.Comparison
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.Comparison
