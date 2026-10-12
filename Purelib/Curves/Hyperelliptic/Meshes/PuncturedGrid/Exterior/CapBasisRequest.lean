module
import Purelib.Algebra.NatCast
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
public import Purelib.Riemann.Topology.PrimitiveSurfaceBudget
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

open Purelib

public section

/-! Coefficient-independent geometric accuracy selection for the complete regular cap. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest

open Purelib.Topology.Polygon.Stokes

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {attached :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared}
  {geometry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached} {coarse : Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length)}
  {depth : Nat} {parameters : Path.Dyadic.RadialTriangles.Parameters depth}
  {index : Nat} {box domain : Rational.Box}

open Purelib.Algebra

open Purelib.Data.Rat.Fraction.Compatibility

set_option genInjectivity false in
/-- One finite depth request for the complete cap and every coefficient
vector. The polynomial ceilings and tolerance are retained as executable data. -/
structure RegularBasisRequest {polynomials :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
    (bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials domain) (count :
      Nat) (target : Fraction.Rational) (minimum : Nat) where
  /-- The retained surface tolerance from the original derivative ceiling and coarse-face count. -/ tolerance :
    Topology.PrimitiveSurfaceBudget.SurfaceTolerance bounds.coefficient (64 * (count : Fraction.Rational)) target
  /-- The cached first sufficient finite depth for the original Taylor tolerance. -/ requiredDepth : Nat
  /-- The required depth is exactly the retained quarter-geometric search result. -/ requiredDepth_eq : requiredDepth =
    Rational.Geometric.Search.firstQuarterBelow (64 * bounds.remainder) minimum (tolerance.epsilon^2)
  /-- The actual retained radial refinement depth. -/ depth : Nat
  /-- The actual depth meets the retained Taylor threshold. -/ requiredDepth_le : requiredDepth ≤ depth
  /-- The actual depth meets the supplied floor. -/ minimum_le : minimum ≤ depth
  /-- The cached squared mesh-diameter ceiling. -/ distance : Fraction.Rational
  /-- The distance is the original quarter-power radius with scale sixty-four. -/ distance_eq : distance =
    Rational.Geometric.Basic.quarterRadius 64 depth
  /-- The retained mesh-distance ceiling is positive. -/ distance_positive : 0 < distance
  /-- The original Taylor remainder times the retained distance fits the squared surface tolerance. -/ taylor :
    bounds.remainder * distance ≤ tolerance.epsilon^2
  /-- The cached complete cap error bound. -/ total : Fraction.Rational
  /-- The total retains the exact coarse-face count, derivative ceiling and allocated tolerance. -/ total_eq : total =
    128 * (count : Fraction.Rational) * (2 * bounds.coefficient + 3) * tolerance.epsilon
  /-- The retained complete error bound is strictly below the supplied target. -/ accurate : total < target

constructive_injectivity RegularBasisRequest

namespace RegularBasisRequest

variable {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index
  box}

/-- Compute one sufficient finite cap depth from the retained basis ceilings and positive target, caching the distance
and complete error bound. -/
@[expose] def build (bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials
  domain) (count : Nat) (target : Fraction.Rational)
    (positive : 0 < target) (minimum : Nat) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest bounds count target minimum := by
  let tolerance := Topology.PrimitiveSurfaceBudget.SurfaceTolerance.build bounds.coefficient (64 * (count :
    Fraction.Rational)) target
    bounds.coefficient_nonnegative (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count))) positive
  let depth := Rational.Geometric.Search.firstQuarterBelow (64 * bounds.remainder) minimum (tolerance.epsilon^2)
  let distance := Rational.Geometric.Basic.quarterRadius 64 depth
  have distancePositive : 0 < distance := Rational.Geometric.Basic.quarterRadius_pos (by decide +kernel) depth
  have taylor : bounds.remainder * distance ≤ tolerance.epsilon^2 := by
    have bound := (Rational.Geometric.Search.firstQuarterBelow_accurate (64 * bounds.remainder)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) bounds.remainder_nonnegative) minimum _
      (Fraction.Order.Arithmetic.pow_pos_direct tolerance.positive 2)).le
    have equal : bounds.remainder * distance = Rational.Geometric.Basic.quarterRadius (64 * bounds.remainder) depth :=
      by
      simp only [distance, Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1
    exact equal.trans_le bound
  let total := 128 * (count : Fraction.Rational) * (2 * bounds.coefficient + 3) * tolerance.epsilon
  exact ⟨tolerance, depth, rfl, depth, le_rfl, Rational.Geometric.Search.firstQuarterBelow_ge _ minimum _, distance,
    rfl, distancePositive, taylor,
    total, rfl, (show total = 2 * (64 * (count : Fraction.Rational)) * (2 * bounds.coefficient + 3) * tolerance.epsilon
      by ring1).trans_lt
      tolerance.accurate⟩

variable {bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials domain}
  {count minimum : Nat} {target : Fraction.Rational}

/-- Reuse the retained tolerance and bounds at a common deeper fan mesh. -/
@[expose] def atDepth (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest bounds
  count target minimum) (depth : Nat)
    (later : request.depth ≤ depth) : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest
      bounds count target minimum := by
  let distance := Rational.Geometric.Basic.quarterRadius 64 depth
  have smaller : distance ≤ request.distance := by
    rw [request.distance_eq]
    exact quarterRadius_antitone (by decide +kernel) later
  exact { request with
    depth := depth
    requiredDepth_le := request.requiredDepth_le.trans later
    minimum_le := request.minimum_le.trans later
    distance := distance
    distance_eq := rfl
    distance_positive := Rational.Geometric.Basic.quarterRadius_pos (by decide +kernel) depth
    taylor := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct smaller bounds.remainder_nonnegative).trans
      request.taylor }

/-- The increasing face count exactly cancels the squared mesh diameter. -/
theorem face_count_cancel (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest
  bounds count target minimum) : ((2 * 4^request.depth : Nat) : Fraction.Rational) * request.distance = 128 := by
  rw [request.distance_eq]
  simp only [NatCast.mul, NatCast.pow, Nat.cast_ofNat, Rational.Geometric.Basic.quarterRadius, -eq_self, -iff_self]
  calc
    _ = 2 * ((64 / (4 : Fraction.Rational)^request.depth) * (4 : Fraction.Rational)^request.depth) := by ring1
    _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ (Fraction.Order.Arithmetic.pow_pos_direct (by decide)
      request.depth).ne']; ring1

end RegularBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
