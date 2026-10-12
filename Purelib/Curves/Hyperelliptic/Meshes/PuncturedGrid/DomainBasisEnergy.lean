module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Content
import Purelib.Polynomial.Geometry.EvaluationLower

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseModelDensity
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Readings.RectangularObservationEnergy
public import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationInterpolation
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Energy.Cell
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Geometry.Rational.Box

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Branches.RectangularSheetGauge

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.RectangularOwnedTriangulation

open Purelib.Riemann.Integration.RectangularSharedPrimitives

open Purelib.Riemann.Normalization.InverseModelDensity

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.AffineBasisEnergy

@[expose] public section

/-!
# Observation energy from the retained standard-differential primitive bank

Every basis reading uses the supplied domain primitives, anchors and offsets,
at one common requested index. Linear combinations do not integrate another
numerator or choose another gauge. The cached affine basis therefore has the
same numerical provenance as the face-corner period comparisons.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedTriangulation ModelTriangle)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Readings.AffineBasisEnergy (AffineBasis)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator_eval)
open Purelib.Riemann.Readings.PreparedObservationInterpolation (eval_reverse_ofFn)
open Purelib.Riemann.Readings.AffineBasisEnergy.AffineBasis (SurfaceBudget)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_mul_right)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face} {sheet :
    Fin 2}
  {domain : PeriodDomain models sheet} {stage : Nat}
  {triangles : List (ModelTriangle domain.geometry)}

set_option genInjectivity false in
/-- The row function selects existing cached domain primitives. The materialized readings and coefficients retain exact
readbacks to those particular caches. -/
structure BasisReadings (cached : (row : Fin genus) → PrimitiveData.DomainPrimitives domain
  (PeriodMatrix.standardDifferential row) stage)
    (surface : RectangularOwnedTriangulation.OwnedTriangulation triangles) where
  /-- The cached standard-differential readings on the supplied exact primitive banks. -/ rows :
    Data.Vector.DependentVector (fun row => RectangularSharedPrimitives.SharedPrimitiveValues (cached row).anchors
    (cached row).offsets surface)
  /-- The retained finite affine basis on the same owned surface triangulation. -/ affine :
    AffineBasisEnergy.AffineBasis surface.mesh.triangulation surface.mesh.coordinate genus
  /-- Every affine-basis vertex value reads back its actual cached primitive row. -/ values_eq : ∀ row vertex,
    affine.values row vertex = (rows.get row).values vertex
  /-- Every affine-basis face coefficient reads back its actual cached primitive row. -/ coefficients_eq : ∀ row face,
    affine.coefficients row face = (rows.get row).faceCoefficients face

constructive_injectivity BasisReadings

namespace BasisReadings

variable {cached : (row : Fin genus) →
  DomainPrimitives domain
  (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential row) stage}
  {surface : OwnedTriangulation triangles}

/-- Materialize all standard-differential rows from the supplied primitive caches and retain exact affine-basis
readbacks. -/
def build (cached : (row : Fin genus) → PrimitiveData.DomainPrimitives domain (PeriodMatrix.standardDifferential row)
  stage)
    (surface : RectangularOwnedTriangulation.OwnedTriangulation triangles) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings cached surface :=
  let rows := DependentVector.ofFn fun row => SharedPrimitiveValues.build (cached row).anchors (cached row).offsets
    surface
  { rows := rows
    affine := ⟨vectorOfFn (fun row => (rows.get row).values), Data.Vector.Basic.vectorOfFn (fun row => (rows.get
      row).faceCoefficients)⟩
    values_eq := fun row vertex => by
      change (Data.Vector.Basic.vectorOfFn (fun row => (rows.get row).values) row) vertex = _
      rw [Data.Vector.Basic.vectorOfFn_apply]
    coefficients_eq := fun row face => by
      change (Data.Vector.Basic.vectorOfFn (fun row => (rows.get row).faceCoefficients) row) face = _
      rw [Data.Vector.Basic.vectorOfFn_apply] }

/-- The affine combination evaluates the exact retained aligned primitives with the supplied coefficients. -/
theorem value_eq (readings : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings cached surface)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (vertex : Fin surface.mesh.vertices.length) :
    readings.affine.value coefficients vertex = FiniteSum.Fin.sumFin (fun row => coefficients row *
      (cached row).anchors.alignedValue (cached row).offsets
        (surface.owners vertex).column (surface.owners vertex).row (surface.mesh.coordinate vertex)) := by
  apply FiniteSum.Fin.sumFin_congr
  intro row
  rw [readings.values_eq, (readings.rows.get row).value_eq, surface.point_eq]

/-- Equal actual surface coordinates give equal retained affine-combination readings. -/
theorem coordinate_consistent (readings : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings
  cached surface) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (first last : Fin surface.mesh.vertices.length) (equal : surface.mesh.coordinate first = surface.mesh.coordinate
      last) :
    readings.affine.value coefficients first = readings.affine.value coefficients last := by
  apply FiniteSum.Fin.sumFin_congr
  intro row
  rw [readings.values_eq, readings.values_eq, (readings.rows.get row).coordinate_consistent first last equal]

/-- All rows share the same retained inverse model; the finite monomial sum is exactly the requested coefficient
polynomial, including the empty basis. -/
theorem coefficient_eq (readings : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings cached
  surface) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (index : Fin (triangles.map ModelTriangle.triangle).length) :
    readings.affine.coefficient coefficients index =
      (EvaluationLower.coefficientPolynomial coefficients).eval (surface.mesh.coordinate
        (surface.mesh.triangulation.faces index).first) *
        ((Transitions.oriented (domain.patch.sheets.refine stage).transitions (domain.patch.sheets.refine
          stage).gauge).ready
          (surface.faceSource index).column (surface.faceSource index).row).model.value.eval
            (surface.mesh.coordinate (surface.mesh.triangulation.faces index).first) := by
  unfold AffineBasis.coefficient
  rw [FiniteSum.Fin.sumFin_congr (fun row => by
    rw [readings.coefficients_eq, SharedPrimitiveValues.faceCoefficients, Data.Vector.Basic.vectorOfFn_apply,
      (cached row).primitives.coefficient_eq, PreparedPrimitiveSamples.differentialNumerator_eval])]
  change FiniteSum.Fin.sumFin (fun row => coefficients row * (_ ^ row.val * _)) = _
  rw [FiniteSum.Fin.sumFin_congr (fun _ => mul_assoc _ _ _ |>.symm), FiniteSum.Fin.sumFin_mul_right]
  congr 1
  exact (PreparedObservationInterpolation.eval_reverse_ofFn coefficients _).symm

variable {box : Box} {mesh :
  ObservationMesh domain.cuts box}

/-- The retained energy-cell density lower bound applies to every actual affine-basis face coefficient. -/
theorem coefficient_lower (readings : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings cached
  mesh.surface)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (cell : PreparedEnergy.SurfaceCell curve
      coefficients)
    (box_eq : cell.box = box) (index : Fin (mesh.triangles.map ModelTriangle.triangle).length) :
    cell.densityLower / 4 ≤ Data.Gaussian.Norm.Basic.normSq (readings.affine.coefficient coefficients index) :=
      by
  rw [readings.coefficient_eq]
  let face := mesh.surface.faceSource index
  let ready := Transitions.oriented
    (domain.patch.sheets.refine stage).transitions (domain.patch.sheets.refine stage).gauge
  have lower := SurfaceCell.densityLower_le_inverseModel
    cell (ready.ready face.column face.row).model
    (box_eq ▸ (mesh.face_inside index).1) (mesh.surface.face_inside index).1
  exact lower

/-- The retained finite affine energy bounds the original energy-cell area times its density lower bound. -/
theorem affineEnergy_lower (readings : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings cached
  mesh.surface)
    (budget : AffineBasis.SurfaceBudget readings.affine) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
      genus)
    (cell : PreparedEnergy.SurfaceCell curve coefficients) (box_eq : cell.box = box) :
    Content.boxContent cell.box * (cell.densityLower / 4) ≤ (budget.sample coefficients).affineEnergy := by
  calc
    _ = FiniteSum.Fin.sumFin (fun index => mesh.faceArea index * (cell.densityLower / 4)) := by
      rw [FiniteSum.Fin.sumFin_mul_right, mesh.faceArea_sum, box_eq]
    _ ≤ FiniteSum.Fin.sumFin (fun index => mesh.faceArea index * Data.Gaussian.Norm.Basic.normSq
      (readings.affine.coefficient coefficients index)) :=
      Order.Positivity.sumFin_mono _ _ (fun index => Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (readings.coefficient_lower coefficients cell box_eq index) (mesh.faceArea_positive index).le)
    _ = _ := by
      rw [(budget.sample coefficients).affineEnergy_eq]
      exact FiniteSum.Fin.sumFin_congr (fun index => by rw [budget.sample_coefficient]; rfl)

/-- The original energy-cell contribution minus the paid coefficient-scaled error bounds the actual retained boundary
energy. -/
theorem contribution_sub_error_le_boundaryEnergy (readings :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings cached mesh.surface)
    (budget : AffineBasis.SurfaceBudget readings.affine) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
      genus)
    (cell : PreparedEnergy.SurfaceCell curve coefficients) (box_eq : cell.box = box) :
    cell.toEnergyCell.contribution / 4 - PreparedObservationCoercivity.coefficientNormSq coefficients * budget.total ≤
      (budget.sample coefficients).boundaryArea.im / 4 := by
  have lower := readings.affineEnergy_lower budget coefficients cell box_eq
  have equal : cell.toEnergyCell.contribution / 4 = Content.boxContent cell.box * (cell.densityLower / 4) := by
    change (Content.boxContent cell.box * cell.densityLower) / 4 = _
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    ring1
  rw [equal]
  exact (Fraction.Order.Arithmetic.add_le_add_right_direct lower
    (-(PreparedObservationCoercivity.coefficientNormSq coefficients * budget.total))).trans (budget.energy_lower
      coefficients)

end BasisReadings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
