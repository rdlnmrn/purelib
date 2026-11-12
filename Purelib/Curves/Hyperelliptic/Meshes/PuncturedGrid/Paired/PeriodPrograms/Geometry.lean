module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty
import Purelib.Polynomial.Geometry.Grid.Walks

/-! # Original nonempty A and full corrected-B walks in the retained paired family

The exact retained walk factories attach the established branch-circuit
nonemptiness to each original period. Corrected B includes its entire
ordered prior correction word, with no shortened reference replacement.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {lifted : LiftedPuncturedGrid base} {bank : BasedBranchBank lifted} {sheet : Fin 2}
variable {ordered : BasedBranchBank.Ordered bank sheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}

/-- The SAME retained canonical A walk is nonempty through its actual ordered branch-pair circuit. -/
theorem aWalk_edgeCount_positive (prepared : Prepared paired) (index : Fin genus) :
    0 < (prepared.aWalk index).closed.walk.edgeCount :=
  Eq.mpr (congrArg (fun size : Nat => 0 < size) (congrArg Walk.edgeCount (prepared.a_walk_eq index)))
    (PeriodNonempty.BasedBranchBank.Pair.closed_edgeCount_positive (paired.row index).row.a)

/-- The SAME retained full corrected-B walk is nonempty, including all original correction occurrences. -/
theorem bWalk_edgeCount_positive (prepared : Prepared paired) (index : Fin genus) :
    0 < (prepared.bWalk index).closed.walk.edgeCount :=
  Eq.mpr (congrArg (fun size : Nat => 0 < size) (congrArg Walk.edgeCount (prepared.b_walk_eq index)))
    (PeriodNonempty.BasedBranchBank.PairedRow.corrected_edgeCount_positive (paired.row index).row)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

end
