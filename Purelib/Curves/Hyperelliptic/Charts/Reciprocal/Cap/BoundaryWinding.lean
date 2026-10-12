module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Constant
import Purelib.Polynomial.Winding.Box.Coordinate
import Purelib.Polynomial.Winding.Box.Product

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary
public import Purelib.Riemann.Curves.OwnerPolynomialImage
import Purelib.Polynomial.Geometry.RegionWinding
import Init.Data.Int.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Tactic.Ring
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction.Order.Arithmetic
open Purelib.Data.List

open Purelib.Data.Rat

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Polynomial

open Purelib.Polynomial.Clearance.Box

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian.Monomial

open Purelib.Polynomial.Winding.Box

open Purelib.Riemann.Curves.OwnerPolynomialImage

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathClosure

open Purelib.Riemann.Paths.PreparedPathWinding

open Purelib.Riemann.Paths.PreparedPathWinding.PreparedClearPathModels

open Purelib.Riemann.Topology

@[expose] public section

/-!
# Exact winding of the retained cap boundary

The regular reciprocal factor has uniform clearance throughout the cap.
The only winding contribution is the displayed coordinate factor in odd
degree. The selected complete boundary consequently has even raw winding.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial)
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Winding.Box.Basic (quadrupledBoxWinding)
open Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate (coordinatePolynomial)

/-- Normalizing a polynomial before a retained coefficient shift preserves the exact shifted polynomial. -/
private theorem shift_normalize (count : Nat) (polynomial : InverseRootPolynomial.Polynomial) :
    DensePolynomial.shift count polynomial.normalize = DensePolynomial.shift count polynomial := by
  simp only [DensePolynomial.shift, DensePolynomial.isZero_normalize, DensePolynomial.normalize_normalize, -eq_self,
    -iff_self]
  rfl

/-- A zero coefficient shift is exactly polynomial normalization. -/
private theorem shift_zero_index (polynomial : InverseRootPolynomial.Polynomial) : DensePolynomial.shift 0 polynomial =
  polynomial.normalize := by
  by_cases zero : polynomial.isZero = true
  · rw [DensePolynomial.shift, if_pos zero, DensePolynomial.normalize_eq_zero_of_isZero zero]
  · rw [DensePolynomial.shift, if_neg zero]
    apply DensePolynomial.ext
    simp only [List.replicate_zero, Append.append_nil, -eq_self, -iff_self]
    rfl

/-- Multiplication by the coordinate polynomial is exactly one coefficient shift. -/
private theorem coordinate_mul (polynomial : InverseRootPolynomial.Polynomial) : Coordinate.coordinatePolynomial *
  polynomial = DensePolynomial.shift 1 polynomial := by
  change DensePolynomial.shift 1 (DensePolynomial.shift 1 0 + DensePolynomial.scale 1 polynomial) +
    DensePolynomial.scale 0 polynomial = DensePolynomial.shift 1 polynomial
  rw [DensePolynomial.shift_zero, DensePolynomial.scale_one_left, DensePolynomial.zero_add_normalize,
    DensePolynomial.normalize_normalize, DensePolynomial.scale_zero_left,
    DensePolynomial.add_zero_normalize, DensePolynomial.normalize_shift,
      shift_normalize]

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}

/-- The retained symmetric cap box has strictly ordered horizontal and vertical sides. -/
theorem box_proper (collar : ReciprocalExteriorCollar.Data curve) : collar.box.Proper := by
  rw [collar.box_eq]
  have positive := ReciprocalExteriorCollar.innerRadius_positive curve
  have nonpositive := Fraction.Order.Arithmetic.neg_le_neg_direct positive.le
  have ordered := (nonpositive.trans_eq (by ring1)).trans_lt positive
  exact ⟨ordered, ordered⟩

/-- The uniformly clear retained regular reciprocal factor has zero quadrupled box winding. -/
private theorem regular_winding (cap : ReciprocalInnerInverse.Data curve collar) :
    Winding.Box.Basic.quadrupledBoxWinding cap.polynomial collar.box = 0 := by
  by_cases zero : cap.polynomial.natDegree = 0
  · have nonzero : cap.polynomial.isZero = false := DensePolynomial.isZero_false_of_eval_ne (by
      rw [cap.polynomial_eq]
      exact (HyperellipticReciprocal.origin_factor curve).1)
    rw [← Winding.Box.Basic.quadrupledBoxWinding_normalize,
      DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero nonzero zero]
    exact Constant.quadrupledBoxWinding_gaussianConstant (DensePolynomial.leadingCoeff_ne_zero nonzero) collar.box
  · exact cap.clearance.winding_zero (Nat.pos_of_ne_zero zero)
      (box_proper collar)

/-- The coordinate polynomial retains the collar's actual positive boundary clearance. -/
private def coordinateClearance (collar : ReciprocalExteriorCollar.Data curve) :
    Boundary.Basic.BoundaryClearance Coordinate.coordinatePolynomial collar.box where
  bound := collar.coordinateBound
  positive := collar.coordinateBound_positive
  lower := fun point boundary => by
    have innerBoundary := boundary
    rw [collar.box_eq] at innerBoundary
    have scalar := ReciprocalExteriorCollar.innerBoundary_coordinate_lower curve (point := point) innerBoundary
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    simpa only [Coordinate.coordinatePolynomial_eval, collar.coordinateBound_eq] using scalar

/-- The coordinate polynomial has quadrupled winding four around the retained symmetric cap box. -/
private theorem coordinate_winding (collar : ReciprocalExteriorCollar.Data curve) :
    Winding.Box.Basic.quadrupledBoxWinding Coordinate.coordinatePolynomial collar.box = 4 := by
  rw [collar.box_eq]
  exact (Coordinate.coordinate_symmetric_normalization (ReciprocalExteriorCollar.innerRadius_positive curve)).1

/-- The exact reversed original polynomial has zero winding on the retained cap boundary. -/
private theorem reversed_winding (cap : ReciprocalInnerInverse.Data curve collar) :
    Winding.Box.Basic.quadrupledBoxWinding (HyperellipticReciprocal.reversed curve.polynomial) collar.box = 0 :=
  (congrArg (fun polynomial => Winding.Box.Basic.quadrupledBoxWinding polynomial collar.box)
    cap.polynomial_eq).symm.trans (regular_winding cap)

/-- Transport the retained cap clearance to the exact reversed original polynomial. -/
private def reversedClearance (cap : ReciprocalInnerInverse.Data curve collar) :
    Boundary.Basic.BoundaryClearance (HyperellipticReciprocal.reversed curve.polynomial) collar.box :=
  (congrArg (fun polynomial => Boundary.Basic.BoundaryClearance polynomial collar.box)
    cap.polynomial_eq) ▸ cap.clearance.toBoundaryClearance

/-- The exact reciprocal radicand's quadrupled box winding is four times its retained origin order. -/
theorem polynomial_winding (cap : ReciprocalInnerInverse.Data curve collar) :
    Winding.Box.Basic.quadrupledBoxWinding (HyperellipticReciprocal.polynomial curve) collar.box =
      4 * (HyperellipticReciprocal.originOrder curve : Int) := by
  cases (HyperellipticReciprocal.origin_factor curve).2 with
  | inl regular =>
      rw [HyperellipticReciprocal.polynomial, regular,
        shift_zero_index,
        Winding.Box.Basic.quadrupledBoxWinding_normalize,
          reversed_winding cap]
      rfl
  | inr branch =>
      rw [HyperellipticReciprocal.polynomial, branch, ←
        coordinate_mul,
        Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances Coordinate.coordinatePolynomial
          (HyperellipticReciprocal.reversed curve.polynomial) collar.box
            (box_proper collar)
          (coordinateClearance collar)
            (reversedClearance cap),
            coordinate_winding,
            reversed_winding cap]
      rfl

/-- One actual retained boundary lap has raw winding four times the original reciprocal origin order. -/
theorem lap_winding (cap : ReciprocalInnerInverse.Data curve collar) :
    (ClearPath.rawWinding (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary.lap collar)) = 4 *
      (HyperellipticReciprocal.originOrder curve : Int) := by
  have equal : (ClearPath.rawWinding (Boundary.lap collar)) = Winding.Box.Basic.quadrupledBoxWinding
    (HyperellipticReciprocal.polynomial curve) collar.box := by
    unfold Boundary.lap Boundary.bottom Boundary.right Boundary.top Boundary.left
    simp only [ClearPath.rawWinding, ClearSegment.rawWinding_eq_coordinateWinding,
      ClearSegment.coordinateWinding]
    rw [Winding.Box.Basic.quadrupledBoxWinding_eq]
    ring1
  exact equal.trans (polynomial_winding cap)

/-- The selected one- or two-lap cap boundary has raw winding eight times the original reciprocal origin order. -/
theorem path_winding (cap : ReciprocalInnerInverse.Data curve collar) :
    (ClearPath.rawWinding (Boundary.path collar)) = 8 * (HyperellipticReciprocal.originOrder curve : Int) := by
  cases (HyperellipticReciprocal.origin_factor curve).2 with
  | inl regular =>
    rw [Boundary.path_regular collar regular, lap_winding cap,
      regular]; rfl
  | inr branch =>
      rw [Boundary.path_branch collar branch, ClearPath.rawWinding_append,
        lap_winding cap, branch]
      rfl

/-- Operational root return for the actual retained boundary: one lap on regular sheets, or two laps around the simple
branch. -/
def rootReturn {cap : ReciprocalInnerInverse.Data curve collar} {differential : Differentials.Basic.Differential genus}
    {owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval collar.box.anchor)}
    (retained : PathCover.Data cap (Boundary.path collar) owner differential) :
    Gaussian.Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName (PreparedPathGluing.finishOwner retained.prepared.traced.prepared))
        (OwnerTraceReadings.ownerName owner) := by
  rw [← retained.prepared.traced.finishOwner_eq]
  exact OwnerPath.rootEquivalent_of_even_winding retained.prepared.traced.trace.get
    (HyperellipticReciprocal.originOrder curve : Int)
    ((TracedPath.winding_original retained.prepared.traced).trans
      (path_winding cap))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary

