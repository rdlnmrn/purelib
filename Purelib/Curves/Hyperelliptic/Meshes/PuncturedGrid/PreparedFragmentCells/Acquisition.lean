module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Classification
public import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

/-! # Retained original grid preparation on an exact supplied parent word

The original split, midpoint-location and regular/hole lookup factories
run once in that order. The complete three results and their original
factory equations retain the exact parent word and canonical grid owner.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.LocatedPrimitiveSplits

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {differential : Differential genus}
variable (base : FramedPuncturedGrid curve branches higher) (axes : PrimitiveAxes base.bank.grid)
variable (parents : List (CenteredEdge curve differential))
variable (inside : ∀ parent ∈ parents, (Cuts.Ambient curve).Contains (parent.edge.point 0) ∧
  (Cuts.Ambient curve).Contains (parent.edge.point 1))

/-- The complete original splitting, cell-location and classification factories on the SAME supplied parent word. -/
@[expose] def Acquisition :=
  Σ splits : {value : PrimitiveSplits axes parents // value = PrimitiveSplits.build axes parents},
  Σ located : {value : LocatedPrimitiveSplits axes splits.val //
    value = LocatedPrimitiveSplits.build base.bank axes splits.val inside},
  {classified : Classifications base.faces located.val //
    classified = LocatedPrimitiveSplits.classify base.faces located.val}

namespace Acquisition

/-- Build the original three geometric caches once without preparing a root, primitive or numerical source again. -/
def build : Acquisition base axes parents inside :=
  let splits := PrimitiveSplits.build axes parents
  let located := LocatedPrimitiveSplits.build base.bank axes splits inside
  let classified := LocatedPrimitiveSplits.classify base.faces located
  ⟨⟨splits, rfl⟩, ⟨located, rfl⟩, ⟨classified, rfl⟩⟩

variable {base axes parents inside} (retained : Acquisition base axes parents inside)

/-- Read the complete original retained grid-axis partitions. -/
@[expose] def splits : PrimitiveSplits axes parents := retained.1.val

/-- Read the complete original retained midpoint/cell locations at those exact partitions. -/
@[expose] def locations : LocatedPrimitiveSplits axes retained.splits := retained.2.1.val

/-- Read the same original regular/hole lookup outcomes at those exact cell locations. -/
@[expose] def classifications : Classifications base.faces retained.locations := retained.2.2.val

/-- The retained splits are exactly the original factory on the SAME original parents. -/
theorem splits_eq : retained.splits = PrimitiveSplits.build axes parents := retained.1.property

/-- The retained locations are exactly the original factory on these same cached splits and endpoints. -/
theorem locations_eq : retained.locations = LocatedPrimitiveSplits.build base.bank axes retained.splits inside :=
  retained.2.1.property

/-- The retained regular/hole product is exactly the original classification factory on those same locations. -/
theorem classifications_eq : retained.classifications = LocatedPrimitiveSplits.classify base.faces retained.locations :=
  retained.2.2.property

end Acquisition
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.LocatedPrimitiveSplits

end
