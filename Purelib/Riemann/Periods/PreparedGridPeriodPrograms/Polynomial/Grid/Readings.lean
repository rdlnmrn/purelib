module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Grid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Data.List.Append
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Primitive.Comparison
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

/-! # Fresh physical period words on one actually acquired reference bank

The complete numerical acquisition and literal same-grid point-list
factory are retained before closing the fresh fragment word. Each actual
fragment acquires its one Finish and two-slot view through the original
closed-word constructor. The actual empty root comparison is retained
without inventing a fragment Point.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine.GridFragments

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)

variable {parameter : Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {framed : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
    {lifted : LiftedPuncturedGrid framed} {vertex : Fin lifted.vertices.count} {source : Differential 1}
    {walk : PeriodWalk framed.bank.grid (lifted.vertices.coordinate vertex)
      (lifted.vertices.owner lifted.frames vertex) source}
    {spine : PolynomialSpine (parameter := parameter) (frame := frame) walk}
    {sourceStart periodStart : Nat} {tolerance : Rational} {positive : 0 < tolerance}
    {selection : PrimitiveSelection walk sourceStart periodStart tolerance positive}
    {domains : FaceDomainBank lifted.frames framed.faces.regulars}
    (fragments : GridFragments lifted vertex walk spine selection domains)

variable {points : List Canonical} {oldTolerance : Rational} {oldStage : Nat} {oldNumerator : CoefficientPolynomial}
    {budgets : FaceMeshBudgets (standardDifferential (0 : Fin 1)) points oldTolerance
      (numerator := oldNumerator) domains}
    {primitives : FacePrimitiveBank (standardDifferential (0 : Fin 1)) oldStage
      (numerator := oldNumerator) domains}
    {later : budgets.index ≤ oldStage}
    (reference : FaceSharedMeshes.Acquisition budgets primitives later)
    (pointPrefix before after : List Canonical)
    (factory : points = pointPrefix ++ (List.ofFn lifted.vertices.coordinate ++
      (before ++ (fragments.points ++ after))))

/-- The original reference execution and exact whole point-list coupling of these fresh physical fragments. -/
@[expose] def Reference.Inputs : Type _ :=
  {inputs : GridFragments lifted vertex walk spine selection domains ×
      FaceSharedMeshes.Acquisition budgets primitives later × List Canonical × List Canonical × List Canonical //
    inputs = (fragments, reference, pointPrefix, before, after) ∧
      points = pointPrefix ++ (List.ofFn lifted.vertices.coordinate ++ (before ++ (fragments.points ++ after)))}

/-- The actual reference acquisition and closed fresh word, with every inherited endpoint membership.

The whole factory chooses these points before the acquisition. It is not
an admission of membership for an unrelated fixed bank. The old numerical
bank, primitive constants, request stages and all original root/Point
owners remain the supplied objects.
-/
@[expose] def Reference : Type _ :=
  Reference.Inputs fragments reference pointPrefix before after ×
  (included : {_value : Unit // ∀ value ∈
    Fragment.PointBanks.RegularPrimitiveSplits.SheetEntries.points fragments.entries, value ∈ points}) ×
  {value : Fragment.SplitSheets.Closed reference.shared fragments.entries fragments.geometry fragments.roots
      included.property //
    value = Fragment.SplitSheets.closedWord reference.shared fragments.entries fragments.geometry fragments.roots
      included.property}

include factory in
/-- Whole point-list coupling includes each actual fresh endpoint, preserving its original repeated slot. -/
private theorem included : ∀ value ∈
    Fragment.PointBanks.RegularPrimitiveSplits.SheetEntries.points fragments.entries, value ∈ points := by
  intro value present
  have actual : value ∈ fragments.points :=
    Eq.mpr (congrArg (fun list : List Canonical => value ∈ list) fragments.points_eq) present
  rewrite [factory]
  exact List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_left _ actual)))

/-- Close the supplied fresh physical fragments once on the SAME actually acquired reference point bank.

The complete original closed-word builder retains each Finish, endpoint
view, adjacent link and literal closing comparison once. Empty fragment
words retain their real root comparison and have no numerical Point.
-/
def onReference : Reference fragments reference pointPrefix before after :=
  let inputs : Reference.Inputs fragments reference pointPrefix before after :=
    ⟨(fragments, reference, pointPrefix, before, after), rfl, factory⟩
  let member : {_value : Unit // ∀ value ∈
      Fragment.PointBanks.RegularPrimitiveSplits.SheetEntries.points fragments.entries, value ∈ points} :=
    ⟨(), included fragments pointPrefix before after factory⟩
  let word : {value : Fragment.SplitSheets.Closed reference.shared fragments.entries fragments.geometry
      fragments.roots member.property //
      value = Fragment.SplitSheets.closedWord reference.shared fragments.entries fragments.geometry
        fragments.roots member.property} :=
    ⟨Fragment.SplitSheets.closedWord reference.shared fragments.entries fragments.geometry
      fragments.roots member.property, rfl⟩
  ⟨inputs, member, word⟩

namespace Reference

variable {fragments reference pointPrefix before after}
    (kept : Reference fragments reference pointPrefix before after)

/-- Read the SAME retained fresh physical geometry and original shared-bank execution as complete data. -/
@[expose] def inputs := kept.1.val

/-- The retained original execution and all three point-list portions have their complete whole-input factory. -/
theorem inputs_eq : kept.inputs = (fragments, reference, pointPrefix, before, after) := kept.1.property.1

include kept in
/-- The actual acquired bank's list is the literal same-grid vertex and fresh endpoint union. -/
theorem pointFactory : points = pointPrefix ++
    (List.ofFn lifted.vertices.coordinate ++ (before ++ (fragments.points ++ after))) := kept.1.property.2

include kept in
/-- Read the actual inherited membership of each original fresh fragment endpoint. -/
theorem included : ∀ value ∈
    Fragment.PointBanks.RegularPrimitiveSplits.SheetEntries.points fragments.entries, value ∈ points :=
  kept.2.1.property

/-- Read the SAME once-prepared original closed fresh word, preserving all literal physical endpoint caches. -/
@[expose] def word : Fragment.SplitSheets.Closed reference.shared fragments.entries fragments.geometry fragments.roots
    kept.included := kept.2.2.val

/-- The full retained fresh word has the exact original closed-word factory on the given original inputs. -/
theorem word_eq : kept.word = Fragment.SplitSheets.closedWord reference.shared fragments.entries fragments.geometry
    fragments.roots kept.included := kept.2.2.property

include kept in
/-- The actual acquired point-bank factory also includes every vertex of this SAME retained grid. -/
theorem vertices_mem (vertex : Fin lifted.vertices.count) : lifted.vertices.coordinate vertex ∈ points :=
  FaceSharedMeshes.Acquisition.vertices_mem lifted.vertices pointPrefix
    (before ++ (fragments.points ++ after)) kept.pointFactory vertex

end Reference

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine.GridFragments

end
