module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.NewtonObservationPartitions
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Readings.ProtectedObservationRegion
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Readings.ContainedObservationEnergy
import Purelib.Polynomial.Geometry.Grid.Rectangle.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Topology.Mesh.CoordinateTriangulation
import Mathlib.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

@[expose] public section

/-!
# Protected observation meshes consuming the retained face domains

The regular-face positions from Newton excision select the actual cached
local model domains. Their cuts automatically subdivide every observation
piece, preserving its complete area. A shared primitive cache at each face
position supplies all standard-differential readings at one common index.
Its cached, coefficient-independent budget gives a lower bound homogeneous
in every coefficient vector. No period-boundary identification or automatic
quantitative decay of that aggregate error is asserted here.
-/

namespace Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub sumFin_mul_right sumFin_mul_left)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Riemann.Readings.AffineBasisEnergy (AffineBasis)
open Purelib.Riemann.Topology.PreparedSurfaceCoercivity (AffineSurfaceSample)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonObservationPartitions.ProtectedObservations (GridPartitions GridPartition)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank DomainPrimitives)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    grid.faces.regulars}

/-- Read the exact original observation cut box at a retained flattened occurrence. -/
def localBox (partitions : GridPartitions observations grid) (index : Fin partitions.indices.length) : Box :=
  (partitions.entries.get partitions.indices[index.val].1).box partitions.indices[index.val].2

/-- Every retained occurrence's original local cut box has strictly ordered sides. -/
theorem localBox_proper (partitions : GridPartitions observations grid) (index : Fin partitions.indices.length) :
    ((localBox partitions) index).Proper :=
  (partitions.entries.get partitions.indices[index.val].1).proper partitions.indices[index.val].2

/-- The local cut box refines its exact original regular-face cell. -/
theorem localBox_refines (partitions : GridPartitions observations grid) (index : Fin partitions.indices.length) :
    ((localBox partitions) index).Refines grid.faces.regulars[(partitions.position index).val].cell.box :=
  (partitions.entries.get partitions.indices[index.val].1).refines_face partitions.indices[index.val].2

open Purelib in
open Purelib.LinearAlgebra.Gaussian in
/-- The flattened retained energy cell has the exact original local cut box. -/
theorem surfaceCells_box (partitions : GridPartitions observations grid)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) (index :
      Fin partitions.indices.length) :
    (partitions.surfaceCells coefficients face index).box = (localBox partitions) index := by
  rw [partitions.surfaceCells_eq, GridPartition.surfaceCells_box]; rfl

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
set_option genInjectivity false in
/-- Observation meshes on the exact local cut boxes and retained original face domains.

Each entry keeps the original flattened occurrence, its cached regular position and the chosen original sheet's domain
cuts. -/
structure LocalMeshes (partitions : GridPartitions observations grid)
    (domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars) (sheet : Fin 2) where
  /-- The dependent observation meshes on the original local cut boxes and retained sheet domains. -/ entries :
    Vector.DependentVector (fun index : Fin partitions.indices.length =>
    ObservationMesh ((domains.get (partitions.position index)).domain sheet).cuts ((localBox partitions) index))

constructive_injectivity LocalMeshes

namespace LocalMeshes

variable {partitions : GridPartitions observations grid} {sheet : Fin 2}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Build the original local observation meshes at a common retained depth.

Each mesh uses the exact source domain's cuts and rectangle points; containment transports through the original cut-box
refinement without changing the regular-face index. -/
def build (partitions : GridPartitions observations grid) (domains :
  Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars) (sheet : Fin 2) (depth : Nat) :
    LocalMeshes partitions domains sheet :=
  ⟨Vector.DependentVector.ofFn fun index => ObservationMesh.build
    ((domains.get (partitions.position index)).domain sheet).cuts ((localBox partitions) index) ((localBox_proper
      partitions) index)
    (fun _ inside => ((domains.get (partitions.position index)).domain sheet).covers (((localBox_refines partitions)
      index).contains inside))
    (((domains.get (partitions.position index)).domain sheet).cuts.rectanglePoints ((localBox partitions) index))
    (fun _ member => member) depth⟩

variable {stage : Nat}

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data
open Purelib.Riemann.Periods
/-- The dependent primitive-bank cache for every original standard differential on the same face domains and stage. -/
abbrev Numerics (domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars) (stage :
  Nat) :=
  Vector.DependentVector (fun row : Fin genus => Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
    (PeriodMatrix.standardDifferential row) stage domains)

/-- Cache the original standard-differential primitive banks at the specified stage. -/
def numerics (domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars) (stage : Nat) :
  Numerics domains stage :=
  Vector.DependentVector.ofFn fun row => Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.build
    (PeriodMatrix.standardDifferential row) stage domains

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Periods in
/-- Read the exact original row, regular position and sheet from the retained numerical cache. -/
def Numerics.atDomain (cache : Numerics domains stage) (position : Fin grid.faces.regulars.length) (sheet : Fin 2)
    (row : Fin genus) : Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives ((domains.get position).domain sheet)
      (PeriodMatrix.standardDifferential row) stage :=
  ((cache.get row).get position).atSheet sheet

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
set_option genInjectivity false in
/-- Cached basis readings on each retained local observation mesh from one original numerical cache.

Every dependent entry keeps its exact original domain, sheet, regular position and local surface; the shared cache
remains the source of all primitive readings. -/
structure Samples (meshes : LocalMeshes partitions domains sheet) (cache : Numerics domains stage) where
  /-- The cached basis readings from the same original numerical bank on each retained local surface. -/ readings :
    Vector.DependentVector (fun index : Fin partitions.indices.length =>
    Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings (cache.atDomain (partitions.position index) sheet)
      (meshes.entries.get index).surface)

constructive_injectivity Samples

namespace Samples

variable {meshes : LocalMeshes partitions domains sheet} {cache : Numerics domains stage}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Cache the local basis readings by restricting the original numerical bank to each exact retained domain and surface.
-/
def ofNumerics (meshes : LocalMeshes partitions domains sheet) (cache : Numerics domains stage) : Samples meshes cache
  :=
  ⟨Vector.DependentVector.ofFn fun index => Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings.build
    (cache.atDomain (partitions.position index) sheet) (meshes.entries.get index).surface⟩

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
set_option genInjectivity false in
/-- A dependent bank of exact local affine-surface budgets and its cached finite total.

Each budget is owned by the original retained basis-reading entry, preserving its local triangulation and separate
triangle error certificates. -/
structure Budget (samples : Samples meshes cache) where
  /-- The dependent affine-surface budgets owned by the exact original local basis-reading entries. -/ entries :
    Vector.DependentVector (fun index => AffineBasisEnergy.AffineBasis.SurfaceBudget (samples.readings.get
    index).affine)
  /-- The cached sum of the original local affine-surface budget totals. -/ total : Fraction.Rational
  /-- The total is exactly the finite sum of the retained budget-bank entries. -/ total_eq : total =
    FiniteSum.Fin.sumFin (fun index => (entries.get index).total)

constructive_injectivity Budget

variable {samples : Samples meshes cache}

open Purelib in
open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
/-- The retained local boundary energies pay a quarter of observation coercivity minus homogeneous error.

The estimate sums the original cell contributions and affine-surface budgets over the same retained flattened
occurrences and coefficient vector. -/
theorem Budget.energy_lower (budget : Budget samples) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
  genus)
    (face : Topology.BranchedCover.Double.Attachment.Face) :
    observations.energy.lower * coefficientNormSq coefficients / 4 - coefficientNormSq coefficients * budget.total ≤
      FiniteSum.Fin.sumFin (fun index => ((budget.entries.get index).sample coefficients).boundaryArea.im / 4) := by
  have localBound := FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun index : Fin partitions.indices.length =>
    (samples.readings.get index).contribution_sub_error_le_boundaryEnergy (budget.entries.get index)
      coefficients (partitions.surfaceCells coefficients face index) ((surfaceCells_box partitions) coefficients face
        index))
  rw [FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_mul_left, ← budget.total_eq] at localBound
  have contributions : FiniteSum.Fin.sumFin (fun index => (partitions.surfaceCells coefficients face
    index).toEnergyCell.contribution / 4) =
      Energy.Prepared.surfaceEnergy (fun index => partitions.surfaceCells coefficients face index) / 4 := by
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    exact FiniteSum.Fin.sumFin_mul_right _ _
  rw [contributions] at localBound
  have lower := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (partitions.uniform_lower coefficients face) (by decide : (0 : Fraction.Rational) ≤ (4 : Fraction.Rational)⁻¹)
  have divided : observations.energy.lower * coefficientNormSq coefficients / 4 ≤
      Energy.Prepared.surfaceEnergy (fun index => partitions.surfaceCells coefficients face index) / 4 := by
    simpa only [Fraction.Field.div_eq_mul_inv_direct] using lower
  exact (Fraction.Order.Arithmetic.add_le_add_right_direct divided
    (-(coefficientNormSq coefficients * budget.total))).trans localBound

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Integration in
set_option genInjectivity false in
/-- Cached local surface samples with exact aggregate lower, error and boundary-energy readbacks.

The entry equation binds every sample to its original budget and coefficient vector. The record separately retains the
coercivity lower term, total certified error and signed boundary energy. -/
structure Bound (budget : Budget samples) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) where
  /-- The cached affine surface samples with each exact original local vertex and face index type. -/ entries :
    Vector.DependentVector (fun index : Fin partitions.indices.length =>
    AffineSurfaceSample (meshes.entries.get index).surface.mesh.vertices.length
      ((meshes.entries.get index).triangles.map RectangularOwnedTriangulation.ModelTriangle.triangle).length)
  /-- Each cached surface sample is the exact sample of its original local budget and coefficient vector. -/ entries_eq
    : ∀ index, entries.get index = (budget.entries.get index).sample coefficients
  /-- The cached quarter-coercivity term for the original coefficient vector. -/ lower : Fraction.Rational
  /-- The lower term is exactly one quarter of observation lower coefficient times coefficient squared norm. -/ lower_eq
    : lower = observations.energy.lower * coefficientNormSq coefficients / 4
  /-- The cached total error of the original retained surface samples. -/ error : Fraction.Rational
  /-- The error equals the finite sum of those exact cached samples' error budgets. -/ error_eq : error =
    FiniteSum.Fin.sumFin (fun index => (entries.get index).errorBudget)
  /-- The cached signed boundary energy of the original retained local samples. -/ boundaryEnergy : Fraction.Rational
  /-- The boundary energy is the finite sum of each exact cached sample's imaginary boundary area divided by four. -/
    boundaryEnergy_eq : boundaryEnergy = FiniteSum.Fin.sumFin (fun index => (entries.get index).boundaryArea.im / 4)

constructive_injectivity Bound

open Purelib.Algebra in
open Purelib.Data in
open Purelib.LinearAlgebra.Gaussian in
/-- Cache the original budget samples and their exact quantitative comparison terms.

The dependent sample bank is built once. Its total error is the coefficient squared norm times the retained budget
total, with proofs linking that formula and boundary energy to the same cached entries. -/
def Budget.bound (budget : Budget samples) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Bound
  budget
  coefficients :=
  let entries := Vector.DependentVector.ofFn fun index => (budget.entries.get index).sample coefficients
  { entries := entries
    entries_eq := Vector.DependentVector.ofFn_get _
    lower := observations.energy.lower * coefficientNormSq coefficients / 4
    lower_eq := rfl
    error := coefficientNormSq coefficients * budget.total
    error_eq := by
      rw [budget.total_eq, ← FiniteSum.Fin.sumFin_mul_left]
      exact FiniteSum.Fin.sumFin_congr (fun index => by rw [Vector.DependentVector.ofFn_get]; rfl)
    boundaryEnergy := FiniteSum.Fin.sumFin (fun index => (entries.get index).boundaryArea.im / 4)
    boundaryEnergy_eq := rfl }

open Purelib.Algebra in
open Purelib.LinearAlgebra.Gaussian in
/-- The retained aggregate error is coefficient squared norm times the exact original budget total. -/
theorem Bound.error_homogeneous {budget : Budget samples} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
  genus}
    (result : Bound budget coefficients) : result.error = coefficientNormSq coefficients * budget.total := by
  rw [result.error_eq, FiniteSum.Fin.sumFin_congr (fun index => congrArg AffineSurfaceSample.errorBudget
    (result.entries_eq index))]
  change FiniteSum.Fin.sumFin (fun index => coefficientNormSq coefficients * (budget.entries.get index).total) = _
  rw [FiniteSum.Fin.sumFin_mul_left, budget.total_eq]

open Purelib in
open Purelib.Algebra in
open Purelib.LinearAlgebra.Gaussian in
/-- The retained lower term minus its exact error is bounded by its cached signed boundary energy. -/
theorem Bound.valid {budget : Budget samples} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    (result : Bound budget coefficients) (face : Topology.BranchedCover.Double.Attachment.Face) :
    result.lower - result.error ≤ result.boundaryEnergy := by
  rw [result.lower_eq, result.error_homogeneous, result.boundaryEnergy_eq,
    FiniteSum.Fin.sumFin_congr (fun index => congrArg (fun entry => entry.boundaryArea.im / 4) (result.entries_eq
      index))]
  exact budget.energy_lower coefficients face

end Samples
end LocalMeshes
end Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
