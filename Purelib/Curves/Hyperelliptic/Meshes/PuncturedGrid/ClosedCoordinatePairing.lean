module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Energy.Polygon

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.GeneratorValuation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.CoordinatePairing
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedPairingMatrix
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Integration

@[expose] public section

/-! Read the geometric pairing identity on the actual retained A/B coordinate rows. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates

open Purelib.Topology.Polygon.Stokes

open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)

local notation (name := _root_.Purelib.Riemann.Meshes.GridClosedCoordinatePairing.termVget)
  "vget" => Data.Vector.get

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {values : Data.Vector Gaussian.Basic.Canonical lifted.cutBoundaryWord.alphabet.count}
  (data : Cut.GeneratorValuation lifted values)

namespace ClosedCoordinates
variable {word : List (OrientedEdge lifted.vertices.count)} (row :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates word integral)

/-- The retained closed-coordinate face correction vanishes under the original generator valuation. -/
theorem
  closed_face_correction_zero
  :
    Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces data.value row.route.correction =
      0 := by
  have vanishes (terms : List (Topology.Surface.Sewing.SewingRetraction.FaceTerm lifted.mesh.triangles.length)) :
      Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces data.value terms = 0 := by
    induction terms with
    | nil => rfl
    | cons term rest ih =>
        change (term.1 : Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue data.value
          (lifted.mesh.triangulation.faces term.2).boundary + _ = 0
        rw [data.face_zero, mul_zero, ih, zero_add]
  exact vanishes row.route.correction

/-- The original closed word value equals the retained integral-coordinate combination of generator values. -/
theorem
  closed_value_eq :
  Topology.Surface.Sewing.SewingRetraction.wordValue data.value word =
    Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine row.coordinates.totals (fun index => vget
      values index) := by
  have reading := row.value_eq data.value data.value_reverse
  rw [row.closed_face_correction_zero data, add_zero] at reading
  apply reading.trans
  apply FiniteSum.Fin.sumFin_congr
  intro index
  dsimp only
  rw [data.generator_readback]

end ClosedCoordinates

/-- The actual A/B word area is the contraction of their retained integral-coordinate wedge. -/
theorem CutRow.closed_area_eq {index :
  Fin genus} (row : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutRow prepared integral index) :
    Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue data.value (prepared.aWord index))
      (Topology.Surface.Sewing.SewingRetraction.wordValue data.value (prepared.bWord index)) =
    Topology.Surface.Word.Pairing.contract (fun first last => row.a.coordinates.totals first * row.b.coordinates.totals
      last -
      row.b.coordinates.totals first * row.a.coordinates.totals last)
      (fun index => Energy.Polygon.energyPrimitivePoint (vget values index)) := by
  rw [row.a.closed_value_eq data, row.b.closed_value_eq data]
  exact Topology.Surface.Cut.CoordinatePairing.area_combine_eq_contract _ _ _

include data

/-- The sum of actual A/B row wedges has the same contraction as the integral cut matrix. -/
theorem
  CutBank.closed_wedge_contraction
  (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) :
    FiniteSum.Fin.sumFin (fun index : Fin genus => Topology.Surface.Word.Pairing.contract
      (fun first last => (cut.rows.get index).a.coordinates.totals first * (cut.rows.get index).b.coordinates.totals
        last -
        (cut.rows.get index).b.coordinates.totals first * (cut.rows.get index).a.coordinates.totals last)
      (fun index => Energy.Polygon.energyPrimitivePoint (vget values index))) =
    Topology.Surface.Word.Pairing.contract (fun first last => cut.integral.paired first last)
      (fun index => Energy.Polygon.energyPrimitivePoint (vget values index)) := by
  apply Eq.trans _ (Hyperelliptic.Meshes.PuncturedGrid.ClosedPairingMatrix.PairedPrepared.pairing_eq_integral data
    prepared cut.integral)
  exact FiniteSum.Fin.sumFin_congr (fun index => ((cut.rows.get index).closed_area_eq data).symm)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
