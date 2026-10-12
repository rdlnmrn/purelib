module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterBounds
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision

public section

/-! Fine local perimeter control on the actual selected annuli. The
excision's disjointness certificate identifies the sum over every annulus
with one selected-face sum, retaining both sheets and signed side values. -/
namespace Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (FacePerimeters)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest (ExteriorBoundaryRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_zero)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {lifted : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank lifted.frames
    grid.faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
  {meshTarget : Rational} {stage : Nat} {cache :
    Numerics domains stage} {i j :
    Fin genus}
  {request : TwoSheetRequest (fun sheet =>
    RegularMeshes.build domains cuts sheet
    coarseDepth) fixed meshTarget}

namespace AllHoleExcision

open Purelib.Curves in
/-- Select regular-face positions retained by at least one annulus of the excision. -/
@[expose] def fineMask (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (position
  : Fin grid.faces.regulars.length) : Bool :=
  excision.entries.any (fun entry => entry.keep (grid.faces.regulars[position.val]'position.isLt))

open Purelib.Curves in
open Purelib.Data in
/-- Sum each retained annulus's selected local face perimeters.

Every term reuses the supplied full side readings on both sheets, with the original signed occurrences. -/
@[expose] def annularPerimeters (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
    (perimeters : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache i
      j) : Gaussian :=
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (excision.entries.map (fun entry => perimeters.selectedPerimeterSum
    (fun position => entry.keep (grid.faces.regulars[position.val]'position.isLt))))

open Purelib.Algebra in
open Purelib.Curves in
/-- Disjoint annuli's perimeter sum equals the single union-selected face perimeter sum. -/
theorem annularPerimeters_eq_selected (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid
  lifted)
    (perimeters : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := request) cache i
      j) :
    annularPerimeters excision perimeters = perimeters.selectedPerimeterSum (fineMask excision) := by
  unfold annularPerimeters Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.selectedPerimeterSum
  rw [Data.Gaussian.Norm.Sum.Indexed.gaussianSum_sumFin]
  apply FiniteSum.Fin.sumFin_congr
  intro position
  rw [Data.Gaussian.Norm.Sum.Indexed.gaussianSum_sumFin]
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  exact Data.Gaussian.Norm.Sum.Basic.gaussianSum_mask_of_pairwise excision.entries
    (fun entry => entry.keep (grid.faces.regulars[position.val]'position.isLt)) _
    (excision.disjoint.imp (fun pair => pair (grid.faces.regulars[position.val]'position.isLt)))

open Purelib.Curves in
open Purelib.Data in
/-- The exterior request bounds the sum of retained annular local face perimeters.

The numerical stage respects the request's ownership floor. Interior face interfaces remain in this sum; the claim uses
the selected-face bound directly. -/
theorem annularPerimeters_bound (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
    {error : Rat.Fraction.Rational}
    (exterior : Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      error)
    (original : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache i j)
    (normalized : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache.normalize i j)
    (later : exterior.prepared.ownership.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (annularPerimeters excision normalized) ≤ error := by
  rw [annularPerimeters_eq_selected excision]
  exact Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterBounds.selected_perimeter_bound exterior original normalized
    (fineMask excision) later

end AllHoleExcision
end Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
