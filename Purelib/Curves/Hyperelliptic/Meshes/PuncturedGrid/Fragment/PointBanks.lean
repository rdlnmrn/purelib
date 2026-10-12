module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedComparison
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries

open Purelib.Geometry.Rectangle.Partition

open Purelib.Riemann.Integration

open Purelib.Riemann.Readings

@[expose] public section

/-!
# Common point banks for the original standard-period fragment spines

The same finite point list may be supplied to every face mesh. Points outside
a face are harmless; every actual analytic endpoint is retained with a
membership certificate. No request polynomial is evaluated by this fold.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragments
  RegularPrimitiveSplits)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    base.faces.regulars}
  {source : Differential genus} {axes :
    PrimitiveAxes base.bank.grid}
  {count : Nat} {target : Rational}

namespace RegularPrimitiveFragments.SheetEntries

variable {parent : CenteredEdge curve source} {partition :
  Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)}
  {request : LocalRequest parent count target}

/-- Collect every actual analytic split endpoint from the retained ordered original fragment requests without evaluating
a polynomial. -/
def points : ∀ {intervals : List PreparedAxisPartitions.Interval}
    {fragments : RegularFaces.RegularPrimitiveFragments axes parent partition intervals},
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets domains request fragments → List
        Data.Gaussian.Basic.Canonical
  | _, _, .nil => []
  | _, _, .cons first rest => first.split.points ++
    points
    rest

end RegularPrimitiveFragments.SheetEntries

namespace RegularPrimitiveSplits.SheetEntries

/-- Concatenate all actual analytic endpoint lists across the retained original parent-request spine without rebuilding
its fragment owners. -/
def points : ∀ {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
  PreparedPrimitiveSplits.PrimitiveSplits axes parents}
    {fragments : RegularFaces.RegularPrimitiveSplits (base := base) axes splits} {requests :
      UniformPreparedRequests.RequestedParents count target parents},
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets domains fragments requests → List
      Data.Gaussian.Basic.Canonical
  | _, _, _, _, .nil => []
  | _, _, _, _, .cons first rest =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks.RegularPrimitiveFragments.SheetEntries.points first
        ++
        points
        rest

end RegularPrimitiveSplits.SheetEntries
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
