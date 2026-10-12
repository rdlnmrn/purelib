module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain

public import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-!
# Automatic finite meshes for primitive neighborhoods

A finite dyadic depth, computed from the shared positive radius, makes every
mesh edge fit inside its left endpoint's primitive patch.  The mesh is the
existing continuation mesh, and its rational-point locator is constructive.
No finite-cover success hypothesis or point-dependent refinement is needed.
-/

public section

namespace Purelib.Riemann.Meshes.UniformPrimitiveMesh

open Purelib
open Purelib.Data
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Data.Gaussian
open Purelib.Approximation.Rational
open Purelib.Polynomial
open Purelib.Geometry.Rational
open Purelib.Riemann.Topology

/-- The original rational Gaussian box carrier. -/
private abbrev Box := Purelib.Geometry.Rational.Box
/-- The canonical Gaussian rational carrier for retained mesh points. -/
private abbrev Gaussian := Basic.Canonical
/-- The original dense Gaussian polynomial carrier. -/
private abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The exact rational carrier for original dyadic parameters. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Branches.ClearSheetContinuation
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}

/-- Both directed half-interval differences equal half the original endpoint difference. -/
private theorem midpoint_differences (left right : Fraction.Rational) :
    midpoint left right - left = (right - left) / 2 ∧
      right - midpoint left right = (right - left) / 2 := by
  have middle : midpoint left right * 2 = left + right := by
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  constructor <;>
    apply Fraction.Field.mul_right_cancel_of_ne (show (2 : Fraction.Rational) ≠ 0 by decide)
  · calc
      _ = midpoint left right * 2 - left * 2 := by ring1
      _ = (right - left) / 2 * 2 := by
        rw [middle, Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
        ring1
  · calc
      _ = right * 2 - midpoint left right * 2 := by ring1
      _ = (right - left) / 2 * 2 := by
        rw [middle, Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
        ring1

/-- Halving a rational displacement advances its squared quarter-radius schedule by one step.

Scalar multiplication distributes the displayed square over the exact inverse of two. The retained power recurrence then
identifies the next original schedule value. -/
private theorem quarterRadius_half_square (value : Fraction.Rational) (depth : Nat) :
    Geometric.Basic.quarterRadius ((value / 2) ^ 2) depth = Geometric.Basic.quarterRadius (value ^ 2) (depth + 1) := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow,
    Fraction.Field.div_eq_mul_inv_direct value 2]
  have inverseSquare : ((2 : Fraction.Rational)⁻¹) ^ 2 = 1 / 4 := by decide
  have distributed : (value * (2 : Fraction.Rational)⁻¹) ^ 2 =
      value ^ 2 * ((2 : Fraction.Rational)⁻¹) ^ 2 := by ring1
  rw [distributed, inverseSquare, pow_succ (1 / 4 : Fraction.Rational) depth]
  ring1

/-- Every retained dyadic edge has the original squared width at its exact subdivision depth.

Original list membership chooses one retained half interval at each step. The midpoint equations and squared-width
recurrence preserve both original endpoint parameters. -/
theorem dyadicEdges_width (depth : Nat) (left right : Endpoint)
    (edge : ParameterEdge) (member : edge ∈ dyadicEdges depth left right) :
    (edge.right.parameter - edge.left.parameter) ^ 2 =
      Geometric.Basic.quarterRadius ((right.parameter - left.parameter) ^ 2) depth := by
  induction depth generalizing left right with
  | zero =>
      have same : edge = { left := left, right := right } := Membership.mem_singleton.mp member
      subst edge
      rw [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct]
  | succ depth ih =>
      rcases Membership.mem_append.mp member with member | member
      · rw [ih _ _ member, (midpoint_differences left.parameter right.parameter).1]
        exact quarterRadius_half_square _ _
      · rw [ih _ _ member, (midpoint_differences left.parameter right.parameter).2]
        exact quarterRadius_half_square _ _

set_option genInjectivity false in
/-- An original mesh edge containing the retained rational parameter, with exact list membership and interval bounds. -/
structure Located (edges : List ParameterEdge) (parameter : Fraction.Rational) where
  /-- The original parameter edge containing the retained parameter. -/ edge : ParameterEdge
  /-- The retained edge belongs to the exact original edge list. -/ member : edge ∈ edges
  /-- The retained parameter lies between that edge's exact original endpoint parameters. -/ between :
    edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter

constructive_injectivity Purelib.Riemann.Meshes.UniformPrimitiveMesh.Located

/-- Locate the retained parameter in the original dyadic edge list by finite midpoint comparisons.

At each depth the exact interval witness selects one original half; the returned edge retains its membership and both
bounds on the same parameter. -/
@[expose] def locateDyadic (depth : Nat) (left right : Endpoint) (parameter : Fraction.Rational)
    (between : left.parameter ≤ parameter ∧ parameter ≤ right.parameter) :
    Located (dyadicEdges depth left right) parameter := by
  cases depth with
  | zero => exact ⟨⟨left, right⟩, List.mem_cons_self .., between⟩
  | succ depth =>
      let middle : Endpoint := ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
      if lower : parameter ≤ middle.parameter then
        let found := locateDyadic depth left middle parameter ⟨between.1, lower⟩
        exact ⟨found.edge, Membership.mem_append.mpr (Or.inl found.member), found.between⟩
      else
        let found := locateDyadic depth middle right parameter ⟨(le_of_not_ge lower), between.2⟩
        exact ⟨found.edge, Membership.mem_append.mpr (Or.inr found.member), found.between⟩

/-- The retained certified zero endpoint of the unit parameter interval. -/
@[expose] def firstEndpoint : Endpoint := ⟨0, by decide⟩
/-- The retained certified one endpoint of the unit parameter interval. -/
@[expose] def lastEndpoint : Endpoint := ⟨1, by decide⟩

set_option genInjectivity false in
/-- A retained uniform subdivision depth making every original segment edge fit inside the common neighborhood radius.

The exact power-of-two edge count is cached, and the original endpoint squared distance at that quarter-radius depth is
strictly below the retained squared radius. -/
structure Mesh {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} (bounds : Bounds segment)
  where
  /-- The retained dyadic subdivision depth. -/ depth : Nat
  /-- The cached number of edges at the retained depth. -/ edgeCount : Nat
  /-- The original edge count equals two raised to the retained depth. -/ edgeCount_eq : edgeCount = 2 ^ depth
  /-- The original segment's squared length at the retained quarter-radius depth is strictly below the squared common
    radius. -/ small : Geometric.Basic.quarterRadius (normSq (finish - start)) depth < bounds.radius ^ 2

constructive_injectivity Purelib.Riemann.Meshes.UniformPrimitiveMesh.Mesh

namespace Mesh

variable {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment polynomial ambient start finish} {bounds : Bounds
  segment}

/-- Search the original segment's squared length for a dyadic depth below the retained positive squared neighborhood
radius. -/
@[expose] def build (bounds : Bounds segment) : Mesh bounds :=
  let depth := Geometric.Search.firstQuarterBelow (normSq (finish - start)) 0 (bounds.radius ^ 2)
  { depth := depth
    edgeCount := 2 ^ depth
    edgeCount_eq := rfl
    small := Geometric.Search.firstQuarterBelow_accurate _ (Basic.Canonical.normSq_nonneg (finish - start)) 0 _
      (Fraction.Order.Arithmetic.pow_pos_direct bounds.radius_positive 2) }

/-- The original dyadic unit-interval edge list at the retained mesh depth. -/
@[expose] def edges (mesh : Mesh bounds) : List ParameterEdge :=
  dyadicEdges mesh.depth firstEndpoint lastEndpoint

/-- The original edge list has exactly the retained mesh's cached edge count. -/
theorem edges_length (mesh : Mesh bounds) : mesh.edges.length = mesh.edgeCount := by
  rw [edges, dyadicEdges_length, mesh.edgeCount_eq]

/-- Locate an original unit-interval parameter in the retained mesh edge list. -/
@[expose] def locate (mesh : Mesh bounds) (parameter : Fraction.Rational) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    Located mesh.edges parameter :=
  locateDyadic mesh.depth firstEndpoint lastEndpoint parameter inside

/-- Every retained mesh edge has endpoint squared distance strictly below the original uniform squared neighborhood
radius. -/
theorem edge_distance (mesh : Mesh bounds) {edge : ParameterEdge} (member : edge ∈ mesh.edges) :
    normSq (segment.pointAt edge.right.parameter - segment.pointAt edge.left.parameter) < bounds.radius ^ 2 := by
  have width := dyadicEdges_width mesh.depth firstEndpoint lastEndpoint edge member
  change (edge.right.parameter - edge.left.parameter) ^ 2 = Geometric.Basic.quarterRadius ((1 - 0 : Fraction.Rational) ^
    2) mesh.depth at width
  have scalar := segment.normSq_pointAt_sub_pointAt edge.right.parameter edge.left.parameter
  rw [Norm.Basic.normSq_eq_canonical
      (segment.pointAt edge.right.parameter - segment.pointAt edge.left.parameter),
    Norm.Basic.normSq_eq_canonical (finish - start)] at scalar
  rw [scalar, width]
  have identity : Geometric.Basic.quarterRadius ((1 - 0 : Fraction.Rational) ^ 2) mesh.depth * normSq (finish - start) =
      Geometric.Basic.quarterRadius (normSq (finish - start)) mesh.depth := by
    rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1
  rw [identity]
  exact mesh.small

/-- Every point between a retained mesh edge's parameters is within its squared uniform radius.

The supplied interval bounds give nonnegative displacements and an ordered square comparison. Multiplication by the
original segment squared length preserves that comparison and the retained mesh radius bound. -/
theorem point_distance (mesh : Mesh bounds) {edge : ParameterEdge} (member : edge ∈ mesh.edges)
    {parameter : Fraction.Rational} (between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) :
    normSq (segment.pointAt parameter - segment.pointAt edge.left.parameter) < bounds.radius ^ 2 := by
  apply lt_of_le_of_lt _ (mesh.edge_distance member)
  have parameterScalar := segment.normSq_pointAt_sub_pointAt parameter edge.left.parameter
  have edgeScalar := segment.normSq_pointAt_sub_pointAt edge.right.parameter edge.left.parameter
  rw [Norm.Basic.normSq_eq_canonical
      (segment.pointAt parameter - segment.pointAt edge.left.parameter),
    Norm.Basic.normSq_eq_canonical (finish - start)] at parameterScalar
  rw [Norm.Basic.normSq_eq_canonical
      (segment.pointAt edge.right.parameter - segment.pointAt edge.left.parameter),
    Norm.Basic.normSq_eq_canonical (finish - start)] at edgeScalar
  rw [parameterScalar, edgeScalar]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct between.1)
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct between.2 _) 2) (Basic.Canonical.normSq_nonneg (finish -
        start))

/-- Every retained parameter in a mesh edge lies in the original prepared seed's continued-neighborhood box at that edge
start.

The exact mesh membership and between witness pay the uniform radius bound, and the retained uniform-box refinement
supplies the original neighborhood containment. -/
theorem point_inside (mesh : Mesh bounds) {edge : ParameterEdge} (member : edge ∈ mesh.edges)
    {owner : SquareRootContinuationChain.Owner (polynomial.eval (segment.pointAt edge.left.parameter))}
    (seed : Bounds.PreparedSeed bounds edge.left.parameter edge.left.inside owner) (count : Nat)
    {parameter : Fraction.Rational} (between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) :
    (seed.neighborhood count).box.Contains (segment.pointAt parameter) := by
  have scalar := (mesh.point_distance member between).le
  rw [← Norm.Basic.normSq_eq_canonical
    (segment.pointAt parameter - segment.pointAt edge.left.parameter)] at scalar
  exact (seed.uniformBox_refines count).contains
    (Box.Square.Centered.centeredBox_contains_of_normSq_sub_le
      bounds.radius_positive.le scalar)

end Mesh

end Purelib.Riemann.Meshes.UniformPrimitiveMesh

end
