module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Content
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Riemann.Topology.PreparedObservationSurface
public import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Riemann.Readings.PreparedObservationBoxes

open Purelib

open Purelib.Algebra

open Purelib.Approximation.Rational

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Integration.Energy

open Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared

open Purelib.Geometry.Rational.Box

open Purelib.Geometry.Rectangle.Partition

open Purelib.LinearAlgebra.Gaussian

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Polynomial

open Purelib.Riemann.Readings

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.PreparedObservationSurface

open Purelib.Riemann.Topology.PreparedSurfacePartitions

open Purelib.Topology.BranchedCover.Double

@[expose] public section

/-!
# Automatic coefficient-independent observation meshes

Cache a dyadic partition of every fixed observation box.  A coefficient
request only instantiates the checked cell densities; it does not rebuild
geometry or choose another radius.  All finite depths retain the same
strictly positive uniform energy constant.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedObservationMesh

open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense
open Purelib.Riemann.Topology.PreparedObservationSurface (ObservationBoxEnergy curveObservationBoxEnergy)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Riemann.Topology.PreparedSurfacePartitions (BoxPartition)

open Purelib.LinearAlgebra
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions

set_option genInjectivity false in
/-- Materialized finite refinement geometry, shared by all coefficient requests. -/
structure ObservationMesh (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (count depth : Nat) where
  /-- The original coefficient-independent observation-box energy certificate. -/ energy :
    PreparedObservationSurface.ObservationBoxEnergy polynomial count
  /-- The retained finite dyadic partition of each original observation box. -/ partitions : Data.Vector
    (PreparedSurfacePartitions.BoxPartition depth) count
  /-- Each cached partition parent is exactly the corresponding original observation box. -/ parent_eq : forall index,
    (partitions index).parent = energy.boxes.box index
  /-- The cached sum of original observation-box content times span. -/ areaSpan : PreparedBoxPartitions.Coordinate
  /-- The cached area-span total equals the explicit finite sum over the original sites. -/ areaSpan_eq : areaSpan =
    FiniteSum.Fin.sumFin (fun index =>
    Content.boxContent (energy.boxes.box index) * PreparedBoxPartitions.span (energy.boxes.box index))

constructive_injectivity ObservationMesh

namespace ObservationMesh

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {count depth : Nat}

/-- Refine the already computed observation geometry to any finite depth. -/
def ofEnergy (energy : PreparedObservationSurface.ObservationBoxEnergy polynomial count) (depth : Nat) :
    Curves.Hyperelliptic.Integration.Observation.PreparedObservationMesh.ObservationMesh polynomial count depth :=
  { energy := energy
    partitions := Data.Vector.Basic.vectorOfFn (fun index => BoxPartition.build (energy.boxes.box index) depth)
    parent_eq := fun index => by rw [Data.Vector.Basic.vectorOfFn_apply]; rfl
    areaSpan := FiniteSum.Fin.sumFin (fun index =>
      Content.boxContent (energy.boxes.box index) * PreparedBoxPartitions.span (energy.boxes.box index))
    areaSpan_eq := rfl }

/-- Every retained site partition has exactly four to the depth leaves. -/
theorem leafCount (mesh : Curves.Hyperelliptic.Integration.Observation.PreparedObservationMesh.ObservationMesh
  polynomial count depth) (index : Fin count) :
    (mesh.partitions index).leaves.length = 4 ^ depth := (mesh.partitions index).length_eq

/-- Leaf rectangles coming from different observation sites remain strictly separated. Within one site they have
disjoint interiors and shared edges. -/
theorem differentSites_separated (mesh :
  Curves.Hyperelliptic.Integration.Observation.PreparedObservationMesh.ObservationMesh polynomial count depth)
    {left right : Fin count} (different : left ≠ right) (leftLeaf rightLeaf : Fin (4 ^ depth)) :
    ((mesh.partitions left).leaf leftLeaf).Separated ((mesh.partitions right).leaf rightLeaf) := by
  apply (mesh.energy.boxes.box_separated different).of_refines
  · rw [<- mesh.parent_eq]
    exact (mesh.partitions left).leaf_refines leftLeaf
  · rw [<- mesh.parent_eq]
    exact (mesh.partitions right).leaf_refines rightLeaf

/-- Geometry-weighted total error over all sites, with the growing leaf count included. This is the standard quarter
rate at twice the spatial depth. -/
theorem totalAreaSpan_quarterRate {index : Nat}
    (mesh : Curves.Hyperelliptic.Integration.Observation.PreparedObservationMesh.ObservationMesh polynomial count (2 *
      index)) (scale : PreparedBoxPartitions.Coordinate) :
    FiniteSum.Fin.sumFin (fun site => PreparedBoxPartitions.sumCells
      (fun small => scale * (Content.boxContent small * PreparedBoxPartitions.span small))
      (mesh.partitions site).leaves) = Geometric.Basic.quarterRadius (scale * mesh.areaSpan) index := by
  have pointwise := FiniteSum.Fin.sumFin_congr
    (left := fun site : Fin count => PreparedBoxPartitions.sumCells
      (fun small => scale * (Content.boxContent small * PreparedBoxPartitions.span small)) (mesh.partitions
        site).leaves)
    (right := fun site : Fin count =>
      (scale * (Content.boxContent (mesh.energy.boxes.box site) * PreparedBoxPartitions.span (mesh.energy.boxes.box
        site))) *
        (1 / 4 : PreparedBoxPartitions.Coordinate) ^ index)
    (fun site : Fin count => by
    rw [(mesh.partitions site).leaves_eq, PreparedBoxPartitions.totalAreaSpan_quarterRate, mesh.parent_eq]
    exact Geometric.Basic.quarterRadius_eq_mul_pow _ index)
  rw [pointwise, FiniteSum.Fin.sumFin_mul_right, FiniteSum.Fin.sumFin_mul_left, <- mesh.areaSpan_eq,
    Geometric.Basic.quarterRadius_eq_mul_pow]

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions in
set_option genInjectivity false in
/-- Cached request-specific leaves and their exact finite total energy. -/
structure Sample (mesh : Curves.Hyperelliptic.Integration.Observation.PreparedObservationMesh.ObservationMesh
  curve.polynomial genus depth)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (face : Attachment.Face) where
  /-- The cached checked surface cells in the original site and leaf order. -/ cells : Data.Vector
    (Data.Vector (PreparedEnergy.SurfaceCell curve coefficients) (4 ^ depth)) genus
  /-- Every cached cell is exactly the density instantiation on its original retained geometric leaf. -/ cells_eq :
    forall site leaf,
    cells site leaf = (mesh.partitions site).surfaceCells
      (ObservationBoxes.surfaceCells mesh.energy.boxes coefficients face site) (by
          simpa only [ObservationBoxes.surfaceCells_box]
            using mesh.parent_eq site) leaf
  /-- The cached rational lower energy of the original request-specific surface cells. -/ energy :
    PreparedBoxPartitions.Coordinate
  /-- The cached request energy equals the finite surface sum of these exact retained cells. -/ energy_eq : energy =
    FiniteSum.Fin.sumFin (fun site =>
    Prepared.surfaceEnergy (fun leaf => cells site leaf))

constructive_injectivity Sample

open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions in
/-- Instantiate densities once, reusing every cached geometric partition. -/
def sample (mesh : Curves.Hyperelliptic.Integration.Observation.PreparedObservationMesh.ObservationMesh curve.polynomial
  genus depth)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (face : Attachment.Face) :
      Sample mesh coefficients face
      :=
  let cells := Data.Vector.Basic.vectorOfFn fun site : Fin genus =>
    (mesh.partitions site).surfaceCells (ObservationBoxes.surfaceCells mesh.energy.boxes coefficients face site) (by
      simpa only [ObservationBoxes.surfaceCells_box] using mesh.parent_eq site)
  { cells := cells
    cells_eq := fun site _ => by rw [Data.Vector.Basic.vectorOfFn_apply]
    energy := FiniteSum.Fin.sumFin (fun site => Prepared.surfaceEnergy (fun leaf => cells site leaf))
    energy_eq := rfl }

namespace Sample

variable {mesh : Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedObservationMesh.ObservationMesh
  curve.polynomial genus depth}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {face : Purelib.Topology.BranchedCover.Double.Attachment.Face}

open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedObservationMesh.ObservationMesh
/-- Each cached surface cell uses its exact original partition leaf box. -/
theorem cell_box (sample : Curves.Hyperelliptic.Integration.Observation.PreparedObservationMesh.ObservationMesh.Sample
  mesh coefficients face) (site : Fin genus) (leaf : Fin (4 ^ depth)) :
    (sample.cells site leaf).box = (mesh.partitions site).leaf leaf := by
  rw [sample.cells_eq, BoxPartition.surfaceCells_box]

/-- The refined mesh retains exactly the original checked lower sum. -/
theorem energy_eq_original (sample :
  Curves.Hyperelliptic.Integration.Observation.PreparedObservationMesh.ObservationMesh.Sample mesh coefficients face) :
    sample.energy = Prepared.surfaceEnergy
      (fun site => ObservationBoxes.surfaceCells mesh.energy.boxes coefficients face site) := by
  rw [sample.energy_eq]
  change FiniteSum.Fin.sumFin (fun site => FiniteSum.Fin.sumFin (fun leaf =>
    Content.boxContent (sample.cells site leaf).box *
      (sample.cells site leaf).densityLower)) = FiniteSum.Fin.sumFin (fun site =>
    Content.boxContent (ObservationBoxes.surfaceCells mesh.energy.boxes coefficients face site).box *
      (ObservationBoxes.surfaceCells mesh.energy.boxes coefficients face site).densityLower)
  apply FiniteSum.Fin.sumFin_congr
  intro site
  calc
    _ = Prepared.surfaceEnergy (fun leaf =>
        (mesh.partitions site).surfaceCells (ObservationBoxes.surfaceCells mesh.energy.boxes coefficients face site)
          (by simpa only [ObservationBoxes.surfaceCells_box] using mesh.parent_eq site) leaf) :=
      FiniteSum.Fin.sumFin_congr (fun leaf => by rw [sample.cells_eq]; rfl)
    _ = _ := by
      rw [BoxPartition.surfaceEnergy_eq, ObservationBoxes.surfaceCells_box mesh.energy.boxes,
        ObservationBoxes.surfaceCells_density mesh.energy.boxes]

/-- The same coefficient-independent constant works at every finite depth. -/
theorem uniform_lower (sample :
  Curves.Hyperelliptic.Integration.Observation.PreparedObservationMesh.ObservationMesh.Sample mesh coefficients face) :
    mesh.energy.lower * PreparedObservationCoercivity.coefficientNormSq coefficients <= sample.energy := by
  rw [sample.energy_eq_original]
  exact mesh.energy.lower_mul_coefficientNorm_le_surfaceEnergy coefficients face

/-- A nonzero original coefficient vector gives strictly positive cached mesh energy. -/
theorem positive (sample : Curves.Hyperelliptic.Integration.Observation.PreparedObservationMesh.ObservationMesh.Sample
  mesh coefficients face)
    (nonzero : Energy.NonzeroGaussianVector coefficients) : 0 < sample.energy := by
  rw [sample.energy_eq_original]
  exact mesh.energy.surfaceEnergy_positive coefficients nonzero face

end Sample

end ObservationMesh

/-- Automatic finite refinement data from just an admissible curve and a depth. -/
def curveObservationMesh {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (depth : Nat) :
    ObservationMesh curve.polynomial genus depth :=
  Curves.Hyperelliptic.Integration.Observation.PreparedObservationMesh.ObservationMesh.ofEnergy
    (PreparedObservationSurface.curveObservationBoxEnergy curve) depth

end Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedObservationMesh
