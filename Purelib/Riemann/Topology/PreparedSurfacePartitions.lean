module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Content
import Purelib.Geometry.Rational.Box.Separation

public import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions

@[expose] public section

/-!
# Cached finite surface refinements preserving the observation energy

Refining a checked surface cell only transports its cached denominator margin
and density; it does not rerun polynomial bounds.  Exact area preservation
therefore preserves the complete local energy lower sum at every depth.
-/

namespace Purelib.Riemann.Topology.PreparedSurfacePartitions

open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (Box Coordinate cells cells_length cells_refine
  cells_proper cells_diagonalSq cells_interiorSeparated sumCells cells_content sumCells_eq_sumFin sumCells_mul_right)

open Purelib.LinearAlgebra

open Purelib.Approximation in
open Purelib.Geometry in
set_option genInjectivity false in
/-- A materialized dyadic box partition with cached area and leaf diagonal.

The retained leaves equal the exact depth-indexed partition of the parent. Area and squared-diagonal caches carry
equations to the same parent and depth. -/
structure BoxPartition (depth : Nat) where
  /-- The retained parent rectangle. -/ parent : Rectangle.Partition.PreparedBoxPartitions.Box
  /-- The materialized ordered list of dyadic leaf rectangles. -/ leaves : List
    Rectangle.Partition.PreparedBoxPartitions.Box
  /-- The retained leaves are exactly the parent's partition at the indexed depth. -/ leaves_eq : leaves =
    Rectangle.Partition.PreparedBoxPartitions.cells depth parent
  /-- The cached rational area of the parent rectangle. -/ area : Rectangle.Partition.PreparedBoxPartitions.Coordinate
  /-- The area cache equals the retained parent's box content. -/ area_eq : area = Rational.Box.Content.boxContent
    parent
  /-- The cached common squared diagonal of the leaf rectangles. -/ leafDiagonalSq :
    Rectangle.Partition.PreparedBoxPartitions.Coordinate
  /-- The diagonal cache equals quarter-geometric decay of the parent's squared diagonal. -/ leafDiagonalSq_eq :
    leafDiagonalSq = Rational.Geometric.Basic.quarterRadius parent.diagonalSq depth

constructive_injectivity BoxPartition

namespace BoxPartition

variable {depth : Nat}

open Purelib.Approximation in
open Purelib.Geometry in
/-- Materialize the dyadic leaves and cache their parent area and common squared diagonal. -/
def build (parent : Rectangle.Partition.PreparedBoxPartitions.Box) (depth : Nat) : BoxPartition depth where
  parent := parent
  leaves := Rectangle.Partition.PreparedBoxPartitions.cells depth parent
  leaves_eq := rfl
  area := Rational.Box.Content.boxContent parent
  area_eq := rfl
  leafDiagonalSq := Rational.Geometric.Basic.quarterRadius parent.diagonalSq depth
  leafDiagonalSq_eq := rfl

open Purelib.Geometry in
/-- The retained leaf list has four to the depth entries. -/
theorem length_eq (partition : BoxPartition depth) : partition.leaves.length = 4 ^ depth := by
  rw [partition.leaves_eq]
  exact Rectangle.Partition.PreparedBoxPartitions.cells_length depth partition.parent

/-- Read a retained leaf using its finite index and the exact cached-list length proof. -/
def leaf (partition : BoxPartition depth) (index : Fin (4 ^ depth)) : Box :=
  partition.leaves[index.val]'(by rw [partition.length_eq]; exact index.isLt)

/-- Every indexed leaf belongs to the retained leaf list. -/
theorem leaf_mem (partition : BoxPartition depth) (index : Fin (4 ^ depth)) :
    partition.leaf index ∈ partition.leaves := List.getElem_mem _

section
open Purelib.Geometry
/-- Every retained leaf refines the same parent rectangle. -/
theorem leaf_refines (partition : BoxPartition depth) (index : Fin (4 ^ depth)) :
    (partition.leaf index).Refines partition.parent := by
  apply Rectangle.Partition.PreparedBoxPartitions.cells_refine depth partition.parent
  rw [<- partition.leaves_eq]
  exact partition.leaf_mem index

/-- A proper parent gives a proper rectangle at every retained leaf. -/
theorem leaf_proper (partition : BoxPartition depth) (proper : partition.parent.Proper)
    (index : Fin (4 ^ depth)) : (partition.leaf index).Proper := by
  apply Rectangle.Partition.PreparedBoxPartitions.cells_proper depth proper
  rw [<- partition.leaves_eq]
  exact partition.leaf_mem index

/-- Every leaf has the retained common squared diagonal. -/
theorem leaf_diagonalSq (partition : BoxPartition depth) (index : Fin (4 ^ depth)) :
    (partition.leaf index).diagonalSq = partition.leafDiagonalSq := by
  rw [partition.leafDiagonalSq_eq]
  apply Rectangle.Partition.PreparedBoxPartitions.cells_diagonalSq depth partition.parent
  rw [<- partition.leaves_eq]
  exact partition.leaf_mem index

/-- Distinct retained leaves have pairwise separated interiors. -/
theorem interiorSeparated (partition : BoxPartition depth) :
    partition.leaves.Pairwise Rational.Box.InteriorSeparated := by
  rw [partition.leaves_eq]
  exact Rectangle.Partition.PreparedBoxPartitions.cells_interiorSeparated depth partition.parent

/-- The sum of all retained leaf areas equals the cached parent area. -/
theorem totalArea_eq (partition : BoxPartition depth) :
    Rectangle.Partition.PreparedBoxPartitions.sumCells Rational.Box.Content.boxContent partition.leaves = partition.area
      := by
  rw [partition.leaves_eq, partition.area_eq]
  exact Rectangle.Partition.PreparedBoxPartitions.cells_content depth partition.parent

end

section
open Purelib.Algebra
open Purelib.Geometry
/-- A box-list sum equals its finite-index sum using the supplied length equality. -/
private theorem sum_eq_of_length {count : Nat} (value : Rectangle.Partition.PreparedBoxPartitions.Box ->
  Rectangle.Partition.PreparedBoxPartitions.Coordinate) (boxes : List Rectangle.Partition.PreparedBoxPartitions.Box)
    (length_eq : boxes.length = count) : Rectangle.Partition.PreparedBoxPartitions.sumCells value boxes =
      FiniteSum.Fin.sumFin (fun index : Fin count => value (boxes[index.val]'(by rw [length_eq]; exact index.isLt))) :=
        by
  subst count
  exact Rectangle.Partition.PreparedBoxPartitions.sumCells_eq_sumFin value boxes

/-- Summing through the finite leaf readback equals summing the retained leaf list. -/
theorem sum_leaf (partition : BoxPartition depth) (value : Rectangle.Partition.PreparedBoxPartitions.Box ->
  Rectangle.Partition.PreparedBoxPartitions.Coordinate) :
    FiniteSum.Fin.sumFin (fun index => value (partition.leaf index)) =
      Rectangle.Partition.PreparedBoxPartitions.sumCells value partition.leaves :=
  (sum_eq_of_length value partition.leaves partition.length_eq).symm

end

open Purelib.Curves in
open Purelib.Geometry in
/-- Transport a certified surface cell to a contained proper rectangle.

Reuse its face, density lower bound and denominator margin; the containment proof transports the original pointwise
certificates without recomputing polynomial bounds. -/
def restrictCell {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    (cell : Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients)
    (small : Rectangle.Partition.PreparedBoxPartitions.Box) (proper : small.Proper) (refines : small.Refines cell.box) :
    Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients where
  face := cell.face
  box := small
  proper := proper
  densityLower := cell.densityLower
  densityLower_nonnegative := cell.densityLower_nonnegative
  denominatorLower := cell.denominatorLower
  denominatorLower_positive := cell.denominatorLower_positive
  denominator_apart := fun point inside => cell.denominator_apart point (refines.contains inside)
  density_below_numerator := fun point inside => cell.density_below_numerator point (refines.contains inside)
  density_valid := fun point inside => cell.density_valid point (refines.contains inside)

section
open Purelib.Curves
open Purelib.Data
/-- Materialize coefficient-specific surface cells on the cached geometric partition.

Each cell reuses the parent's density and denominator certificates, while its box is the corresponding retained leaf.
The parent equality ties both owners together. -/
def surfaceCells {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    (partition : BoxPartition depth) (cell : Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
      coefficients)
    (parent_eq : partition.parent = cell.box) :
    Data.Vector (Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) (4 ^
      depth) :=
  Vector.Basic.vectorOfFn fun index => restrictCell cell (partition.leaf index)
    (partition.leaf_proper (by rw [parent_eq]; exact cell.proper) index)
    (by rw [<- parent_eq]; exact partition.leaf_refines index)

/-- A restricted surface cell's box is the exact retained partition leaf. -/
theorem surfaceCells_box {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    (partition : BoxPartition depth) (cell : Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
      coefficients)
    (parent_eq : partition.parent = cell.box) (index : Fin (4 ^ depth)) :
    (partition.surfaceCells cell parent_eq index).box = partition.leaf index := by
  rw [surfaceCells, Vector.Basic.vectorOfFn_apply]
  rfl

/-- Every restricted surface cell reuses the original density lower bound. -/
theorem surfaceCells_density {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    (partition : BoxPartition depth) (cell : Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
      coefficients)
    (parent_eq : partition.parent = cell.box) (index : Fin (4 ^ depth)) :
    (partition.surfaceCells cell parent_eq index).densityLower = cell.densityLower := by
  rw [surfaceCells, Vector.Basic.vectorOfFn_apply]
  rfl

end

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Geometry in
/-- Dyadic restriction preserves the checked surface-energy contribution exactly.

Every leaf reuses the same density bound, and the retained leaf areas sum to the parent area. -/
theorem surfaceEnergy_eq {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    (partition : BoxPartition depth) (cell : Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
      coefficients)
    (parent_eq : partition.parent = cell.box) :
    Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy (fun index => partition.surfaceCells cell parent_eq index) =
      Rational.Box.Content.boxContent cell.box * cell.densityLower := by
  change FiniteSum.Fin.sumFin (fun index =>
    Rational.Box.Content.boxContent (partition.surfaceCells cell parent_eq index).box *
      (partition.surfaceCells cell parent_eq index).densityLower) = _
  calc
    _ = FiniteSum.Fin.sumFin (fun index => Rational.Box.Content.boxContent (partition.leaf index) * cell.densityLower)
      :=
      FiniteSum.Fin.sumFin_congr (fun index => by rw [partition.surfaceCells_box, partition.surfaceCells_density])
    _ = Rectangle.Partition.PreparedBoxPartitions.sumCells (fun box => Rational.Box.Content.boxContent box *
      cell.densityLower) partition.leaves :=
      partition.sum_leaf (fun box => Rational.Box.Content.boxContent box * cell.densityLower)
    _ = partition.area * cell.densityLower := by
      rw [Rectangle.Partition.PreparedBoxPartitions.sumCells_mul_right, partition.totalArea_eq]
    _ = _ := by rw [partition.area_eq, parent_eq]

end BoxPartition

end Purelib.Riemann.Topology.PreparedSurfacePartitions
