module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Clearance.Box.Region

import Purelib.Riemann.Meshes.AnalyticGridFaces
public import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Normalization.InverseRootComparison
public import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Refinement
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Uniform finite inverse-root models on regular faces

The full-face clearance bounds every inverse-root seed, independently of its
chosen owner.  One computed dyadic depth therefore makes each child rectangle
small enough for a constant seed and all subsequent polynomial Newton steps.
Point queries follow one finite subdivision path without allocating the full
mesh.  Owners are retained as sheet data; agreement across different cells
and the global surface/period comparison remain separate obligations.
-/

namespace Purelib.Riemann.Normalization.RegularFaceInverseModels

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (Seed Owner)
open Purelib.Riemann.Normalization.InverseRootComparison (normalized_value_bound)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_antitone)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow firstQuarterBelow_accurate)

open Purelib.Polynomial.Clearance.Box in
/-- The original polynomial region-clearance certificate on the retained box. -/
abbrev Clearance := Region.RegionClearance

variable {polynomial : Polynomial} {box : Purelib.Riemann.Normalization.InverseRootPolynomial.Box}

open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- Cached scalar bounds for uniform inverse-root models on subboxes of a cleared original box.

The polynomial Lipschitz bound and clearance determine a squared seed bound, variation and a positive allowed squared
diameter. -/
structure Bounds (clearance : Clearance polynomial box) where
  /-- The cached polynomial Lipschitz bound on the original box. -/ slope : Coordinate
  /-- The cached slope equals the original dense polynomial Lipschitz bound. -/ slope_eq : slope =
    Bounds.Box.denseLipschitzBound polynomial box
  /-- The retained slope is strictly positive. -/ slope_positive : 0 < slope
  /-- The cached squared seed bound from the original clearance. -/ seedSquared : Coordinate
  /-- The squared seed cache equals four divided by the original clearance bound. -/ seedSquared_eq : seedSquared = 4 /
    clearance.bound
  /-- The retained squared seed bound is strictly positive. -/ seedSquared_positive : 0 < seedSquared
  /-- The cached product controlling polynomial movement against the seed bound. -/ variation : Coordinate
  /-- The variation cache is exactly the retained slope times squared seed bound. -/ variation_eq : variation = slope *
    seedSquared
  /-- The retained variation is nonnegative. -/ variation_nonnegative : 0 ≤ variation
  /-- The cached positive squared-diameter allowance for inverse models. -/ diameter : Coordinate
  /-- The diameter equals one sixty-fourth divided by the retained variation plus one. -/ diameter_eq : diameter = (1 /
    64) / (variation + 1)
  /-- The retained squared-diameter allowance is strictly positive. -/ diameter_positive : 0 < diameter

constructive_injectivity Bounds

namespace Bounds

variable {clearance : Clearance polynomial box}

open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
/-- Compute the exact inverse-model bounds from the original polynomial and retained region clearance.

The cached slope, reciprocal-clearance seed bound and variation determine the positive diameter, with their defining
equations and sign certificates retained. -/
@[expose] def build (clearance : Clearance polynomial box) : Bounds clearance :=
  let slope := Bounds.Box.denseLipschitzBound polynomial box
  have slopePositive := Bounds.Box.denseLipschitzBound_pos polynomial box
  let seedSquared : Coordinate := 4 / clearance.bound
  have seedPositive : 0 < seedSquared := Fraction.Order.Field.div_pos_direct (by decide) clearance.positive
  let variation := slope * seedSquared
  have nonnegative : 0 ≤ variation := Fraction.Order.Arithmetic.mul_nonneg_direct slopePositive.le seedPositive.le
  let diameter : Coordinate := (1 / 64) / (variation + 1)
  have positive : 0 < diameter := Fraction.Order.Field.div_pos_direct (by decide +kernel)
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct nonnegative (by decide))
  ⟨slope, rfl, slopePositive, seedSquared, rfl, seedPositive, variation, rfl, nonnegative, diameter, rfl, positive⟩

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A normalized inverse-root seed inside the original cleared box satisfies the retained squared seed bound. -/
theorem seed_squared_le (bounds : Bounds clearance) {point : Gaussian}
    (inside : box.Contains point) (seed : Seed (polynomial.eval point)) :
    Data.Gaussian.Norm.Basic.normSq seed.value ^ 2 ≤ bounds.seedSquared := by
  have small : Data.Gaussian.Norm.Basic.normSq (1 - polynomial.eval point * seed.value ^ 2) ≤ 1 / 16 :=
    (Norm.Basic.normSq_eq_canonical _).trans_le
      (seed.residual_small.trans (by decide +kernel : (1 / 64 : Fraction.Rational) ≤ 1 / 16))
  have normalized := normalized_value_bound small
  rw [bounds.seedSquared_eq]
  apply (Fraction.Order.Field.le_div_iff_pos clearance.positive).2
  calc
    _ = clearance.bound * Data.Gaussian.Norm.Basic.normSq seed.value ^ 2 := by ring1
    _ ≤ Data.Gaussian.Norm.Basic.normSq (polynomial.eval point) * Data.Gaussian.Norm.Basic.normSq seed.value ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (clearance.lower point inside)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    _ ≤ 4 := normalized

open Purelib.Data.Rat in
/-- The diameter allowance bounds variation times the subbox diameter by one sixty-fourth.

The retained nonnegative variation and positive diameter transfer the
supplied subbox bound through the defining reciprocal allowance. -/
theorem variation_paid (bounds : Bounds clearance) {diameter : Coordinate}
    (small : diameter ≤ bounds.diameter) : bounds.variation * diameter ≤ 1 / 64 := by
  have translated := Fraction.Order.Arithmetic.add_le_add_right_direct
    (show (0 : Coordinate) ≤ 1 by decide) bounds.variation
  have enlarged : bounds.variation ≤ bounds.variation + 1 :=
    calc
      _ = 0 + bounds.variation := (Fraction.Field.zero_add _).symm
      _ ≤ 1 + bounds.variation := translated
      _ = bounds.variation + 1 := Fraction.Field.add_comm _ _
  calc
    _ ≤ bounds.variation * bounds.diameter :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small bounds.variation_nonnegative
    _ ≤ (bounds.variation + 1) * bounds.diameter :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        enlarged bounds.diameter_positive.le
    _ = 1 / 64 := by
      rw [bounds.diameter_eq, Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _
        (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
          bounds.variation_nonnegative (by decide)).ne'

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- A seed at an interior point gives inverse-root residual at most one sixteenth throughout a sufficiently small
refining box.

The retained clearance controls the seed size, and the original polynomial variation and diameter certificates control
movement away from the seed point. -/
theorem residual_small (bounds : Bounds clearance) {inner : Purelib.Geometry.Rational.Box}
    (refines : inner.Refines box) (small : inner.diagonalSq ≤ bounds.diameter)
    {center : Gaussian} (centerInside : inner.Contains center)
    (seed : Seed (polynomial.eval center)) {point : Gaussian} (inside : inner.Contains point) :
    Data.Gaussian.Norm.Basic.normSq (1 - polynomial.eval point * seed.value ^ 2) ≤ 1 / 16 := by
  have variation := Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound polynomial
    (refines.contains centerInside) (refines.contains inside)
  rw [← bounds.slope_eq] at variation
  have distance := Box.normSq_sub_le_diagonalSq centerInside inside
  have movement := variation.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    distance bounds.slope_positive.le)
  have perturbation : Data.Gaussian.Norm.Basic.normSq ((polynomial.eval center - polynomial.eval point) * seed.value ^
    2) ≤ 1
    / 64 := by
    rw [Norm.Basic.normSq_mul, Power.normSq_pow]
    calc
      _ ≤ (bounds.slope * inner.diagonalSq) * bounds.seedSquared :=
        Fraction.Order.Arithmetic.mul_le_mul_direct movement
          (bounds.seed_squared_le (refines.contains centerInside) seed)
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
          (Fraction.Order.Arithmetic.mul_nonneg_direct bounds.slope_positive.le inner.diagonalSq_nonneg)
      _ = bounds.variation * inner.diagonalSq := by rw [bounds.variation_eq]; ring1
      _ ≤ 1 / 64 := bounds.variation_paid small
  have identity : 1 - polynomial.eval point * seed.value ^ 2 =
      (1 - polynomial.eval center * seed.value ^ 2) +
        (polynomial.eval center - polynomial.eval point) * seed.value ^ 2 := by ring1
  have seedSmall : Data.Gaussian.Norm.Basic.normSq (1 - polynomial.eval center * seed.value ^ 2) ≤ 1 / 64 :=
    (Norm.Basic.normSq_eq_canonical _).trans_le seed.residual_small
  rw [identity]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add seedSmall perturbation) (by decide)).trans_eq (by
        decide +kernel : (2 : Coordinate) * (1 / 64 + 1 / 64) = 1 / 16))

end Bounds

/-- A subbox refining the original cleared box with squared diameter within the retained model allowance. -/
structure CellGeometry {clearance : Clearance polynomial box} (bounds : Bounds clearance) (inner :
  Purelib.Geometry.Rational.Box) where
  /-- The original inner box refines the original cleared outer box. -/ refines : inner.Refines box
  /-- The original inner squared diameter satisfies the retained allowance. -/ small : inner.diagonalSq ≤
    bounds.diameter

open Purelib.Polynomial in
set_option genInjectivity false in
/-- An inverse-root model on an original small subbox, retaining its center and exact seed.

The model value is exactly the constant polynomial of the stored seed; its certificate comes from the original geometric
refinement and residual bound. -/
structure SeededCell {clearance : Clearance polynomial box} (bounds : Bounds clearance) (inner :
  Purelib.Geometry.Rational.Box) where
  /-- The exact retained subbox refinement and diameter certificate. -/ geometry : CellGeometry bounds inner
  /-- The original point at which the inverse-root seed is retained. -/ center : Gaussian
  /-- The retained center belongs to the original subbox. -/ centerInside : inner.Contains center
  /-- The original inverse-root seed at the polynomial value of the retained center. -/ seed : Seed (polynomial.eval
    center)
  /-- The certified inverse-root polynomial model on the original subbox. -/ model : Model polynomial inner
  /-- The stored model value is exactly the constant polynomial of the retained seed. -/ value_eq : model.value =
    Dense.Basic.DensePolynomial.constant seed.value

constructive_injectivity SeededCell

namespace SeededCell

variable {clearance : Clearance polynomial box} {bounds : Bounds clearance} {inner :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Box}

open Purelib.Data.Gaussian in
/-- Construct the constant inverse-root model from the original small-cell geometry and interior seed.

The model retains the supplied seed and center, using the uniform residual estimate over the exact refining subbox. -/
@[expose] def ofSeed (geometry : CellGeometry bounds inner) (center : Gaussian) (centerInside : inner.Contains center)
    (seed : Seed (polynomial.eval center)) : SeededCell bounds inner :=
  ⟨geometry, center, centerInside, seed, Model.ofSeed polynomial inner seed.value
    (fun _ inside => (Norm.Basic.normSq_eq_canonical _).symm.trans_le
      (bounds.residual_small geometry.refines geometry.small centerInside seed inside)), rfl⟩

/-- Construct the small-cell inverse model from its original root owner at an interior point.

The original owner produces the retained inverse-root seed, which is passed unchanged to the seeded-cell construction.
-/
@[expose] def ofOwner (geometry : CellGeometry bounds inner) (center : Gaussian) (centerInside : inner.Contains center)
    (owner : Owner (polynomial.eval center)) : SeededCell bounds inner :=
  ofSeed geometry center centerInside (Seed.ofOwner owner)

end SeededCell

open Purelib.Approximation.Rational in
set_option genInjectivity false in
/-- A dyadic box partition depth with a retained geometric smallness certificate for the original model bounds. -/
structure Mesh {clearance : Clearance polynomial box} (bounds : Bounds clearance) where
  /-- The retained dyadic partition depth. -/ depth : Nat
  /-- The original inner squared diameter satisfies the retained allowance. -/ small : Geometric.Basic.quarterRadius
    box.diagonalSq depth ≤ bounds.diameter

constructive_injectivity Mesh

namespace Mesh

variable {clearance : Clearance polynomial box} {bounds : Bounds clearance}

section
open Purelib.Approximation.Rational
/-- Choose a dyadic mesh depth whose squared cell diameter is strictly below the original model allowance.

The geometric search retains the original box diameter and positive bound, supplying the exact smallness certificate for
the chosen depth. -/
@[expose] def build (bounds : Bounds clearance) : Mesh bounds :=
  let depth := Geometric.Search.firstQuarterBelow box.diagonalSq 0 bounds.diameter
  ⟨depth, (Geometric.Search.firstQuarterBelow_accurate _ box.diagonalSq_nonneg 0 _ bounds.diameter_positive).le⟩

/-- Increase a retained mesh depth while preserving its original model bounds and geometric smallness. -/
@[expose] def atDepth (mesh : Mesh bounds) (depth : Nat) (later : mesh.depth ≤ depth) : Mesh bounds :=
  ⟨depth, (quarterRadius_antitone box.diagonalSq_nonneg later).trans mesh.small⟩

end

section
open Purelib.Geometry.Rectangle.Partition
/-- The ordered dyadic cells at the retained depth of the original cleared box. -/
@[expose] def cells (mesh : Mesh bounds) : List Box :=
  PreparedBoxPartitions.cells mesh.depth box

/-- Every original retained mesh cell satisfies the exact model diameter allowance. -/
theorem cells_small (mesh : Mesh bounds) {inner : Purelib.Geometry.Rational.Box} (member : inner ∈ mesh.cells) :
    inner.diagonalSq ≤ bounds.diameter := by
  rw [PreparedBoxPartitions.cells_diagonalSq mesh.depth box member]
  exact mesh.small

end

set_option genInjectivity false in
/-- A retained mesh cell containing the original requested point, with its membership certificate. -/
structure Located (mesh : Mesh bounds) (point : Gaussian) where
  /-- The retained original cell box selected from the mesh. -/ box : Purelib.Geometry.Rational.Box
  /-- The selected box belongs to the exact retained mesh cell list. -/ member : box ∈ mesh.cells
  /-- The original requested point belongs to the retained selected cell. -/ contains : box.Contains point

constructive_injectivity Located

open Purelib.Geometry.Rectangle.Partition
/-- Locate an original point in the exact retained dyadic partition and keep its cell membership and containment. -/
@[expose] def locate (mesh : Mesh bounds) (point : Gaussian) (inside : box.Contains point) : Located mesh point :=
  ⟨PreparedBoxPartitions.locate mesh.depth box point,
    PreparedBoxPartitions.locate_mem mesh.depth box point,
    PreparedBoxPartitions.locate_contains mesh.depth inside⟩

/-- Restrict the original polynomial clearance to a retained mesh cell through its exact refinement. -/
@[expose] def clearanceAt (mesh : Mesh bounds) {inner : Purelib.Geometry.Rational.Box} (member : inner ∈ mesh.cells) :
  Clearance polynomial inner
  :=
  clearance.restrict (PreparedBoxPartitions.cells_refine mesh.depth box member)

/-- Package the original mesh cell's refinement and diameter bound as model geometry. -/
theorem cellGeometry (mesh : Mesh bounds) {inner : Purelib.Geometry.Rational.Box} (member : inner ∈ mesh.cells) :
  CellGeometry bounds inner :=
  ⟨PreparedBoxPartitions.cells_refine mesh.depth box member, mesh.cells_small member⟩

end Mesh

end Purelib.Riemann.Normalization.RegularFaceInverseModels
