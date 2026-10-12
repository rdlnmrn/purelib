module
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.SquareRootTrace
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Affine.Segment
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Path.Segment
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Polynomial.Winding.Polygon.Comparison
import Purelib.Riemann.Paths.OwnerLoopMonodromy

public import Purelib.Riemann.RootContinuation.CoordinateRootReference
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

@[expose] public section

/-!
# The polynomial-value image of a retained root trace

Each original trace edge stays within its cached variation bound. The chord
between its two polynomial values stays within that same bound, so the same
root readings certify an edge over the coordinate polynomial. The local
winding corrections agree at both endpoints. This construction is used in
erased closure proofs, without acquiring another numerical root trace.
-/

namespace Purelib.Riemann.Curves.OwnerPolynomialImage

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense

open Purelib.Riemann.RootContinuation.SquareRootTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName OwnerTail)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerLink OwnerPath)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Data.Gaussian.Cast.Path (ofCoordinate)
open Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate (coordinatePolynomial coordinatePolynomial_eval)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Scaling a Gaussian displacement by a parameter between zero and one does not increase its squared norm. -/
private theorem scaled_movement (value : Basic.Canonical) (time : Fraction.Rational) (inside : 0 ≤ time ∧ time ≤ 1) :
    normSq (value * Cast.Path.ofCoordinate time) ≤ normSq value := by
  have squareLe : time ^ 2 ≤ 1 := by
    simpa only [one_pow] using Fraction.Order.Arithmetic.pow_le_pow_direct inside.1 inside.2 2
  have coordinateNorm : normSq (Cast.Path.ofCoordinate time) = time ^ 2 := by
    simp only [Cast.Path.ofCoordinate, normSq]
    ring1
  have productNorm := Norm.Basic.normSq_mul value (Cast.Path.ofCoordinate time)
  rw [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at productNorm
  rw [productNorm, coordinateNorm]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareLe (Basic.Canonical.normSq_nonneg
    value)).trans_eq (by ring1)

namespace Edge

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {first last start
  finish :
  Purelib.Data.Gaussian.Basic.Canonical}

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Transport the original root continuation to the coordinate-polynomial image of its endpoints.

The construction retains the original root owner data and checked edge certificates while replacing the geometric
endpoints by their exact polynomial values. -/
def valueImage (edge : Edge polynomial first last start finish) :
    Edge Monomial.Coordinate.coordinatePolynomial first last (polynomial.eval start) (polynomial.eval finish) where
  data := {
    rootNorm := edge.data.rootNorm
    rootNorm_eq := edge.data.rootNorm_eq
    distance := edge.data.distance
    distance_eq := edge.data.distance_eq
    residual := edge.data.residual
    residual_eq := by rw [Monomial.Coordinate.coordinatePolynomial_eval]; exact edge.data.residual_eq
    variation := Dense.Basic.DensePolynomial.scale (polynomial.eval finish - polynomial.eval start)
      Monomial.Coordinate.coordinatePolynomial
    variation_eq := by
      intro time
      rw [Dense.Basic.DensePolynomial.eval_scale, Monomial.Coordinate.coordinatePolynomial_eval,
        Monomial.Coordinate.coordinatePolynomial_eval, Monomial.Coordinate.coordinatePolynomial_eval]
      unfold Affine.line
      ring1
    movementBound := edge.data.movementBound
    movementBound_valid := by
      intro time inside
      rw [Dense.Basic.DensePolynomial.eval_scale, Monomial.Coordinate.coordinatePolynomial_eval]
      have endpoint := edge.data.movement_le (time := 1) (by constructor <;> decide)
      rw [Affine.Segment.line_segment_one] at endpoint
      exact (scaled_movement _ time inside).trans endpoint }
  checked := edge.checked

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The original checked edge and its polynomial-value image have the same doubled winding. -/
theorem valueImage_winding (edge : Edge polynomial first last start finish) :
    (Path.Segment.segment Monomial.Coordinate.coordinatePolynomial (polynomial.eval start) (polynomial.eval
      finish)).doubledWinding =
      (Path.Segment.segment polynomial start finish).doubledWinding := by
  have source := Winding.Polygon.Comparison.segmentRaw_eq_of_homotopy edge.homotopy
  have image := Winding.Polygon.Comparison.segmentRaw_eq_of_homotopy (Edge.valueImage edge).homotopy
  simp only [Monomial.Coordinate.coordinatePolynomial_eval] at image
  omega

end Edge

section
open Purelib.Data.Gaussian
/-- Transport the original square-root owner along an exact parameter equality. -/
public def reindexOwner {first last : Basic.Canonical} (equal : first = last) (owner : Owner first) : Owner last := by
  cases equal
  exact owner

/-- Exact parameter transport preserves the original square-root owner's operational name. -/
private theorem reindexOwner_name {first last : Basic.Canonical} (equal : first = last) (owner : Owner first) :
    ownerName (reindexOwner equal owner) = ownerName owner := by
  cases equal
  rfl

/-- Transport the retained original refinement tail along its exact parameter equality. -/
public def reindexTail {first last : Basic.Canonical} (equal : first = last) {owner : Owner first}
    (tail : OwnerTail owner) : OwnerTail (reindexOwner equal owner) := by
  cases equal
  exact tail

/-- Parameter transport preserves the original retained tail's first stage. -/
private theorem reindexTail_first {first last : Basic.Canonical} (equal : first = last) {owner : Owner first}
    (tail : OwnerTail owner) : (reindexTail equal tail).first = tail.first := by
  cases equal
  rfl

/-- Recover the original-tail reading from its exact parameter-reindexed counterpart. -/
public def originalReading {first last : Basic.Canonical} (equal : first = last) {owner : Owner first}
    {tail : OwnerTail owner} (reading : OwnerTail.Reading (reindexTail equal tail)) : OwnerTail.Reading tail := by
  cases equal
  exact reading

/-- Recovering an original-tail reading preserves its exact retained stage. -/
public theorem originalReading_index {first last : Basic.Canonical} (equal : first = last) {owner : Owner first}
    {tail : OwnerTail owner} (reading : OwnerTail.Reading (reindexTail equal tail)) :
    (originalReading equal reading).index = reading.index := by
  cases equal
  rfl

/-- Recovering an original-tail reading preserves its exact Gaussian value. -/
public theorem originalReading_value {first last : Basic.Canonical} (equal : first = last) {owner : Owner first}
    {tail : OwnerTail owner} (reading : OwnerTail.Reading (reindexTail equal tail)) :
    (originalReading equal reading).value = reading.value := by
  cases equal
  rfl

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
/-- View the same original square-root owner under coordinate-polynomial evaluation equality. -/
def valueOwner {parameter : Basic.Canonical} (owner : Owner parameter) : Owner
  (Monomial.Coordinate.coordinatePolynomial.eval parameter) :=
  reindexOwner (Monomial.Coordinate.coordinatePolynomial_eval parameter).symm owner

open Purelib.Data.Gaussian in
/-- The coordinate-polynomial view has the exact original owner's operational name. -/
theorem valueOwner_name {parameter : Basic.Canonical} (owner : Owner parameter) : ownerName (valueOwner owner) =
  ownerName owner :=
  reindexOwner_name _ _

namespace OwnerLink

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {start finish :
  Purelib.Data.Gaussian.Basic.Canonical}
  {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}

open Purelib.Polynomial.Dense.Gaussian
/-- Transport the exact original owner link to its polynomial-value endpoint image.

The original retained tails, readiness indices and realized checked edge are reindexed only by coordinate-polynomial
evaluation equality; no root or tail is selected again. -/
def valueImage (link : OwnerLink polynomial start finish left right) :
    OwnerLink Monomial.Coordinate.coordinatePolynomial (polynomial.eval start) (polynomial.eval finish) (valueOwner
      left) (valueOwner right) := by
  let firstEq := (Monomial.Coordinate.coordinatePolynomial_eval (polynomial.eval start)).symm
  let lastEq := (Monomial.Coordinate.coordinatePolynomial_eval (polynomial.eval finish)).symm
  refine ⟨reindexTail firstEq link.leftTail, reindexTail lastEq link.rightTail, link.leftIndex,
    link.rightIndex,
    (by rw [reindexTail_first]; exact link.left_ge), (by rw [reindexTail_first]; exact link.right_ge), ?_⟩
  intro first last firstLater lastLater
  let originalFirst := originalReading firstEq first
  let originalLast := originalReading lastEq last
  have firstReady : link.leftIndex ≤ originalFirst.index := by rw [originalReading_index]; exact firstLater
  have lastReady : link.rightIndex ≤ originalLast.index := by rw [originalReading_index]; exact lastLater
  have edge := Edge.valueImage (link.realize originalFirst originalLast firstReady lastReady)
  rw [originalReading_value, originalReading_value] at edge
  exact edge

/-- The original retained owner link and its polynomial-value image have the same doubled winding. -/
theorem valueImage_winding (link : OwnerLink polynomial start finish left right) :
    (Path.Segment.segment Monomial.Coordinate.coordinatePolynomial (polynomial.eval start) (polynomial.eval
      finish)).doubledWinding =
      (Path.Segment.segment polynomial start finish).doubledWinding :=
  Edge.valueImage_winding (link.realize (OwnerTail.Reading.acquire link.leftTail link.leftIndex link.left_ge)
    (OwnerTail.Reading.acquire link.rightTail link.rightIndex link.right_ge) le_rfl le_rfl)

end OwnerLink

namespace OwnerPath

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}

open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
/-- Map the original ordered owner-link path through polynomial evaluation.

The recursive construction keeps the same link order and retained endpoint owners, using their exact
coordinate-polynomial parameter transports. -/
def valueImage : ∀ {start finish : Basic.Canonical} {left : Owner (polynomial.eval start)} {right : Owner
  (polynomial.eval finish)},
    OwnerPath polynomial start left finish right →
      OwnerPath Monomial.Coordinate.coordinatePolynomial (polynomial.eval start) (valueOwner left) (polynomial.eval
        finish) (valueOwner right)
  | _, _, _, _, .nil point owner => .nil (polynomial.eval point) (valueOwner owner)
  | _, _, _, _, .cons link tail => .cons (OwnerLink.valueImage link) (valueImage tail)

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The original polynomial path and its coordinate-polynomial value image have the same doubled winding. -/
theorem valueImage_winding : ∀ {start finish : Basic.Canonical} {left : Owner (polynomial.eval start)} {right : Owner
  (polynomial.eval finish)}
    (path : OwnerPath polynomial start left finish right),
    Winding.Polygon.Basic.chainRaw Monomial.Coordinate.coordinatePolynomial (polynomial.eval start) (valueImage
      path).vertices =
      Winding.Polygon.Basic.chainRaw polynomial start path.vertices
  | _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, .cons link tail => by
      change (Path.Segment.segment Monomial.Coordinate.coordinatePolynomial _ _).doubledWinding + _ =
        (Path.Segment.segment polynomial _ _).doubledWinding + _
      rw [OwnerLink.valueImage_winding link, valueImage_winding tail]

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- An original closed root-owner path with even winding returns an operationally equivalent root name.

The explicit winding multiple is transported through the same coordinate-polynomial image and its root reference,
preserving the original initial and final owner names. -/
def rootEquivalent_of_even_winding {base : Basic.Canonical} {first last : Owner (polynomial.eval base)}
    (path : OwnerPath polynomial base first base last) (turns : Int)
    (even : Winding.Polygon.Basic.chainRaw polynomial base path.vertices = 8 * turns) :
    Equivalence.NamedEquivalent (ownerName last) (ownerName first) := by
  have imageEven : Winding.Polygon.Basic.chainRaw Monomial.Coordinate.coordinatePolynomial (polynomial.eval base)
      (valueImage path).vertices = 8 * turns := (valueImage_winding path).trans even
  have returned := OwnerLoopMonodromy.OwnerPath.rootEquivalent_of_even_with_reference
    (CoordinateRootReference.build (polynomial.eval base) first.parameterNonzero) (valueImage path) turns imageEven
  rw [valueOwner_name, valueOwner_name] at returned
  exact returned

end OwnerPath
end Purelib.Riemann.Curves.OwnerPolynomialImage
