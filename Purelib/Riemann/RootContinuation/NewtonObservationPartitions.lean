module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Content
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Polynomial.Geometry.Grid.Rectangle.Cuts
public import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Readings.ProtectedObservationRegion
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Readings.ContainedObservationEnergy
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Riemann.Readings.PreparedObservationBoxes
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Topology.PreparedObservationSurface
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data

public section

/-!
# Observation lower sums on the actual retained Newton grid

Each protected observation rectangle is partitioned at the existing grid
lines. Every proper piece caches its original regular-face position and
refines both that face and the observation rectangle. Exact finite area
additivity transfers the original checked density and homogeneous positive
lower sum without a caller-supplied coverage or area-equality certificate.
-/

namespace Purelib.Riemann.RootContinuation.NewtonObservationPartitions

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq coefficientNormSq_positive)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_mul_right)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations (RegularLocation
  RetainedTriangle)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (Sewn)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational}

namespace ProtectedObservations

open Purelib.Data in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- A grid partition of one original protected observation box with retained regular-face indices.

Each cut box keeps the original grid and observation-site owner and refines the exact regular cell at its cached bounded
position. -/
structure GridPartition (observations : ProtectedObservations original) (grid : NewtonGrid preparation target radius)
    (site : Fin genus) where
  /-- The original grid partition of this exact retained observation square. -/ cuts :
    Geometry.Grid.Rectangle.Cuts.Partition grid.shrunk.prepared.grid (observations.energy.box site)
  /-- The cached original regular-face position for every retained cut box. -/ positions : Data.Vector (Fin
    grid.faces.regulars.length) cuts.boxes.length
  /-- Each cut box refines the original regular cell at its exact cached position. -/ refines_face : ∀ index : Fin
    cuts.boxes.length,
    cuts.boxes[index.val].Refines grid.faces.regulars[(positions index).val].cell.box

constructive_injectivity GridPartition

namespace GridPartition

variable {observations : ProtectedObservations original} {grid : NewtonGrid preparation target radius} {site : Fin
  genus}

open Purelib.Data in
open Purelib.Polynomial in
/-- Partition one original protected box and cache its containing regular-face positions.

The original grid cuts and exact box centers determine each location; every retained cut box is certified to refine the
corresponding original regular cell. -/
@[expose] def build (observations : ProtectedObservations original) (grid : NewtonGrid preparation target radius) (site
  : Fin genus) :
    GridPartition observations grid site := by
  let cuts := Geometry.Grid.Rectangle.Cuts.Partition.build grid.shrunk.prepared.grid
    (observations.energy.box site) (observations.energy.box_proper site)
  let locate (index : Fin cuts.boxes.length) := observations.locate grid site
    (Geometry.Grid.Rectangle.Cuts.center cuts.boxes[index.val])
    ((cuts.refines (List.getElem_mem _)).contains (Geometry.Grid.Rectangle.Cuts.center_inside (cuts.proper
      (List.getElem_mem _))))
  refine ⟨cuts, Vector.Basic.vectorOfFn (fun index => (locate index).position), ?_⟩
  intro index
  apply Eq.mpr (congrArg (fun position : Fin grid.faces.regulars.length =>
    cuts.boxes[index.val].Refines grid.faces.regulars[position.val].cell.box)
    (Vector.Basic.vectorOfFn_apply (fun index => (locate index).position) index))
  exact Geometry.Grid.Rectangle.Cuts.Partition.refines_cell cuts (List.getElem_mem _)
    grid.faces.regulars[(locate index).position.val].member
    (Geometry.Grid.Rectangle.Cuts.center_strict (cuts.proper (List.getElem_mem _))) (locate index).contains

/-- Read one cut box by its original bounded index in the retained observation partition. -/
@[expose] def box (partition : GridPartition observations grid site) (index : Fin partition.cuts.boxes.length) : Box :=
  partition.cuts.boxes[index.val]

/-- Every original observation cut box has strictly ordered sides. -/
theorem proper (partition : GridPartition observations grid site) (index : Fin partition.cuts.boxes.length) :
    (partition.box index).Proper := partition.cuts.proper (List.getElem_mem _)

/-- Every retained cut box refines its exact original protected observation square. -/
theorem refines_observation (partition : GridPartition observations grid site) (index : Fin partition.cuts.boxes.length)
  :
    (partition.box index).Refines (observations.energy.box site) := partition.cuts.refines (List.getElem_mem _)

open Purelib.Algebra in
open Purelib.Geometry.Rational in
open Purelib.Geometry.Rectangle.Partition in
/-- The sum of the original partition-box areas equals the retained observation area. -/
theorem area_eq (partition : GridPartition observations grid site) :
    FiniteSum.Fin.sumFin (fun index => Box.Content.boxContent (partition.box index)) = observations.energy.area := by
  change FiniteSum.Fin.sumFin (fun index : Fin partition.cuts.boxes.length =>
    Box.Content.boxContent partition.cuts.boxes[index.val]) = _
  rw [← PreparedBoxPartitions.sumCells_eq_sumFin, partition.cuts.area_eq, observations.energy.boxContent_eq_area]

open Purelib.Polynomial in
/-- Retain the original regular-face position containing the exact cut-box center. -/
@[expose] def location (partition : GridPartition observations grid site) (index : Fin partition.cuts.boxes.length) :
    RegularLocation grid (Geometry.Grid.Rectangle.Cuts.center (partition.box index)) :=
  ⟨partition.positions index, (partition.refines_face index).contains (Geometry.Grid.Rectangle.Cuts.center_inside
    (partition.proper index))⟩

open Purelib in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Topology in
/-- Cache the original certified observation energy cells restricted to their retained cut boxes. -/
@[expose] def surfaceCells (partition : GridPartition observations grid site)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) :
    Data.Vector (Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) partition.cuts.boxes.length :=
  let original := observations.energy.surfaceCell coefficients face site
  Vector.Basic.vectorOfFn fun index => PreparedSurfacePartitions.BoxPartition.restrictCell original
    (partition.box index) (partition.proper index) (partition.refines_observation index)

section
open Purelib
open Purelib.Data
open Purelib.LinearAlgebra.Gaussian
/-- The cached restricted energy cell keeps its exact original cut box. -/
theorem surfaceCells_box (partition : GridPartition observations grid site)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) (index :
      Fin partition.cuts.boxes.length) :
    (partition.surfaceCells coefficients face index).box = partition.box index := by
  rw [surfaceCells, Vector.Basic.vectorOfFn_apply]; rfl

/-- Partition restriction preserves the original observation site's certified density lower bound. -/
theorem surfaceCells_density (partition : GridPartition observations grid site)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) (index :
      Fin partition.cuts.boxes.length) :
    (partition.surfaceCells coefficients face index).densityLower =
      observations.energy.original.boxes.numeratorLower coefficients site /
        observations.energy.original.boxes.denominatorScale := by
  rw [surfaceCells, Vector.Basic.vectorOfFn_apply]; rfl

end

open Purelib in
open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Geometry.Rational in
open Purelib.LinearAlgebra.Gaussian in
/-- The cut-box energy equals the original observation area times its retained site density. -/
theorem surfaceEnergy_eq (partition : GridPartition observations grid site)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) :
    Energy.Prepared.surfaceEnergy (fun index => partition.surfaceCells coefficients face index) =
      observations.energy.area *
        (observations.energy.original.boxes.numeratorLower coefficients site /
          observations.energy.original.boxes.denominatorScale) := by
  change FiniteSum.Fin.sumFin (fun index => Box.Content.boxContent (partition.surfaceCells coefficients face index).box
    *
    (partition.surfaceCells coefficients face index).densityLower) = _
  calc
    _ = FiniteSum.Fin.sumFin (fun index => Box.Content.boxContent (partition.box index) *
        (observations.energy.original.boxes.numeratorLower coefficients site /
          observations.energy.original.boxes.denominatorScale)) :=
      FiniteSum.Fin.sumFin_congr (fun index => by rw [partition.surfaceCells_box, partition.surfaceCells_density])
    _ = _ := by rw [FiniteSum.Fin.sumFin_mul_right, partition.area_eq]

variable {lifted : LiftedPuncturedGrid grid.punctured}
  {localValues : Fin lifted.mesh.triangles.length → Purelib.Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}
  {sample : Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch localValues}
  {excision : Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted}

open Purelib.Polynomial in
open Purelib.Riemann.Topology in
/-- Recover the original surviving sewn triangle at the retained cut-box center and sheet. -/
@[expose] def retainedTriangle (partition : GridPartition observations grid site)
    (sewn : NewtonSewnExcision.AllHoleExcision.Sewn excision sample) (index : Fin partition.cuts.boxes.length)
    (sheet : Fin 2) (upper : Bool) : RetainedTriangle sewn (partition.location index) sheet upper :=
  observations.retainedTriangle sewn site (Geometry.Grid.Rectangle.Cuts.center (partition.box index))
    ((partition.refines_observation index).contains (Geometry.Grid.Rectangle.Cuts.center_inside (partition.proper
      index)))
    (partition.location index) sheet upper

end GridPartition

open Purelib.Data in
set_option genInjectivity false in
/-- Dependent partitions for all original observation sites with their retained flattened occurrence list.

Each occurrence contains its original site and bounded local cut-box index; the stored equality specifies the exact
site-major enumeration. -/
structure GridPartitions (observations : ProtectedObservations original) (grid : NewtonGrid preparation target radius)
  where
  /-- The dependent bank of partitions indexed by the original observation sites. -/ entries : Vector.DependentVector
    (fun site => GridPartition observations grid site)
  /-- The retained ordered occurrences of original site and bounded local cut-box indices. -/ indices : List (Sigma fun
    site => Fin (entries.get site).cuts.boxes.length)
  /-- The occurrence list is exactly the site-major flattening of the original local index lists. -/ indices_eq :
    indices = (List.ofFn fun site => List.ofFn fun index : Fin (entries.get site).cuts.boxes.length =>
    Sigma.mk site index).flatten

constructive_injectivity GridPartitions

namespace GridPartitions

variable {observations : ProtectedObservations original} {grid : NewtonGrid preparation target radius}

open Purelib.Data in
/-- Cache every original observation-site partition and its exact site-major bounded occurrence list. -/
@[expose] def build (observations : ProtectedObservations original) (grid : NewtonGrid preparation target radius) :
    GridPartitions observations grid :=
  let entries := Vector.DependentVector.ofFn (GridPartition.build observations grid)
  ⟨entries, (List.ofFn fun site => List.ofFn fun index : Fin (entries.get site).cuts.boxes.length =>
    Sigma.mk site index).flatten, rfl⟩

open Purelib in
open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.LinearAlgebra.Gaussian in
/-- The sum of site-grouped partition energies equals the original observation-cell energy. -/
theorem groupedEnergy_eq (partitions : GridPartitions observations grid)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) :
    FiniteSum.Fin.sumFin (fun site => Energy.Prepared.surfaceEnergy
      (fun index => (partitions.entries.get site).surfaceCells coefficients face index)) =
      Energy.Prepared.surfaceEnergy (fun site => observations.energy.surfaceCells coefficients face site) := by
  rw [observations.energy.surfaceEnergy_eq, ← FiniteSum.Fin.sumFin_mul_left]
  exact FiniteSum.Fin.sumFin_congr (fun site => (partitions.entries.get site).surfaceEnergy_eq coefficients face)

open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)

open Purelib.Algebra in
open Purelib.Data.Rat in
/-- Summing retained flattened occurrences equals the original nested site and cut-box sums. -/
theorem sum_indices (partitions : GridPartitions observations grid)
    (value : (Sigma fun site => Fin (partitions.entries.get site).cuts.boxes.length) → Fraction.Rational) :
    FiniteSum.Fin.sumFin (fun index : Fin partitions.indices.length => value partitions.indices[index.val]) =
      FiniteSum.Fin.sumFin (fun site => FiniteSum.Fin.sumFin (fun index => value ⟨site, index⟩)) := by
  calc
    _ = FiniteSum.Rational.Squares.coordinateSum (partitions.indices.map value) :=
      (FiniteSum.Rational.Squares.coordinateSum_map_eq_sumFin partitions.indices value).symm
    _ = FiniteSum.Rational.Squares.coordinateSum (((List.ofFn fun site => List.ofFn fun index : Fin
      (partitions.entries.get site).cuts.boxes.length =>
        Sigma.mk site index).flatten).map value) := congrArg (fun items => FiniteSum.Rational.Squares.coordinateSum
          (items.map value)) partitions.indices_eq
    _ = _ := (FiniteSum.Rational.Squares.coordinateSum_map_flatten_ofFn _ value).trans (FiniteSum.Fin.sumFin_congr (fun
      site : Fin genus =>
      FiniteSum.Rational.Squares.coordinateSum_map_ofFn (fun index : Fin (partitions.entries.get site).cuts.boxes.length
        => Sigma.mk site index) value))

open Purelib in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data in
open Purelib.LinearAlgebra.Gaussian in
/-- Cache the original site-local energy banks and read them through the exact retained flattened occurrences.

The construction preserves each original site and cut-box index and reuses its bank entry in the flattened vector. -/
@[expose] def surfaceCells (partitions : GridPartitions observations grid)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) :
    Data.Vector (Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) partitions.indices.length :=
  let banks := Vector.DependentVector.ofFn fun site => (partitions.entries.get site).surfaceCells coefficients face
  Vector.Basic.vectorOfFn fun index : Fin partitions.indices.length =>
    let occurrence := partitions.indices[index.val]
    banks.get occurrence.1 occurrence.2

open Purelib in
open Purelib.Data in
open Purelib.LinearAlgebra.Gaussian in
/-- Each flattened cached cell is the exact original site-local cached cell selected by its retained occurrence. -/
theorem surfaceCells_eq (partitions : GridPartitions observations grid)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) (index :
      Fin partitions.indices.length) :
    partitions.surfaceCells coefficients face index =
      (partitions.entries.get partitions.indices[index.val].1).surfaceCells coefficients face
        partitions.indices[index.val].2 := by
  rw [surfaceCells, Vector.Basic.vectorOfFn_apply]
  dsimp only
  rw [Vector.DependentVector.ofFn_get]

/-- Read the original regular-face position attached to a retained flattened cut-box occurrence. -/
@[expose] def position (partitions : GridPartitions observations grid) (index : Fin partitions.indices.length) : Fin
  grid.faces.regulars.length :=
  let occurrence := partitions.indices[index.val]
  (partitions.entries.get occurrence.1).positions occurrence.2

open Purelib in
open Purelib.LinearAlgebra.Gaussian in
/-- Every flattened cached energy cell refines the exact original regular cell at its retained position. -/
theorem surfaceCells_refines_face (partitions : GridPartitions observations grid)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) (index :
      Fin partitions.indices.length) :
    (partitions.surfaceCells coefficients face index).box.Refines grid.faces.regulars[(partitions.position
      index).val].cell.box := by
  rw [partitions.surfaceCells_eq, GridPartition.surfaceCells_box]
  exact (partitions.entries.get partitions.indices[index.val].1).refines_face partitions.indices[index.val].2

open Purelib in
open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Geometry.Rational in
open Purelib.LinearAlgebra.Gaussian in
/-- Flattening the exact retained site partitions preserves the original observation surface energy. -/
theorem surfaceEnergy_eq (partitions : GridPartitions observations grid)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) :
    Energy.Prepared.surfaceEnergy (fun index => partitions.surfaceCells coefficients face index) =
      Energy.Prepared.surfaceEnergy (fun site => observations.energy.surfaceCells coefficients face site) := by
  rw [← partitions.groupedEnergy_eq coefficients face]
  change FiniteSum.Fin.sumFin (fun index => Box.Content.boxContent (partitions.surfaceCells coefficients face index).box
    *
    (partitions.surfaceCells coefficients face index).densityLower) = _
  calc
    _ = FiniteSum.Fin.sumFin (fun index : Fin partitions.indices.length =>
        let cell := (partitions.entries.get partitions.indices[index.val].1).surfaceCells coefficients face
          partitions.indices[index.val].2
        Box.Content.boxContent cell.box * cell.densityLower) :=
      FiniteSum.Fin.sumFin_congr (fun index => by rw [partitions.surfaceCells_eq])
    _ = _ := partitions.sum_indices (fun occurrence =>
      let cell := (partitions.entries.get occurrence.1).surfaceCells coefficients face occurrence.2
      Box.Content.boxContent cell.box * cell.densityLower)

open Purelib in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.LinearAlgebra.Gaussian in
/-- The flattened observation partition preserves the original uniform coefficient-norm energy lower bound. -/
theorem uniform_lower (partitions : GridPartitions observations grid)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) :
    observations.energy.lower * coefficientNormSq coefficients ≤
      Energy.Prepared.surfaceEnergy (fun index => partitions.surfaceCells coefficients face index) := by
  rw [partitions.surfaceEnergy_eq]
  exact observations.uniform_lower coefficients face

open Purelib in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
/-- A nonzero original coefficient vector has positive energy on the retained partition cells. -/
theorem positive_energy (partitions : GridPartitions observations grid)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (nonzero : Energy.NonzeroGaussianVector
      coefficients)
    (face : Topology.BranchedCover.Double.Attachment.Face) : 0 < Energy.Prepared.surfaceEnergy
      (fun index => partitions.surfaceCells coefficients face index) :=
  (Fraction.Order.Arithmetic.mul_pos_direct observations.energy.lower_positive (coefficientNormSq_positive
    nonzero)).trans_le
    (partitions.uniform_lower coefficients face)

/-- Cut boxes from distinct original observation sites remain separated. -/
theorem different_sites_separated (partitions : GridPartitions observations grid) {first last : Fin genus} (different :
  first ≠ last)
    (left : Fin (partitions.entries.get first).cuts.boxes.length) (right : Fin (partitions.entries.get
      last).cuts.boxes.length) :
    ((partitions.entries.get first).box left).Separated ((partitions.entries.get last).box right) :=
  (observations.energy.boxes_separated different).of_refines
    ((partitions.entries.get first).refines_observation left) ((partitions.entries.get last).refines_observation right)

end GridPartitions
end ProtectedObservations
end Purelib.Riemann.RootContinuation.NewtonObservationPartitions
