module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Program
import Purelib.Data.List.Membership

/-! # Original fine-layer source factory receipts without a second time query

Every midpoint split stores its source once. Left children retain their
parent's complete original Reading; right children retain the original
midpoint query. The source receipt follows those SAME stored children and
never invokes another producer at runtime.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {radicand : CoefficientPolynomial}
variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}

namespace Piece

/-- The complete source of an original retained piece is its actual original requested-time query factory. -/
@[irreducible, expose] def Queried (piece : Piece data actual accuracy) : Prop :=
  piece.source = Transport.Reading.build actual piece.span.lower
    (piece.within piece.span.lower ⟨Fraction.Order.Basic.le_refl _, piece.span.valid⟩)

/-- Read the whole original source factory identity without replacing the stored piece or its query. -/
theorem Queried.readback {piece : Piece data actual accuracy} (queried : piece.Queried) :
    piece.source = Transport.Reading.build actual piece.span.lower
      (piece.within piece.span.lower ⟨Fraction.Order.Basic.le_refl _, piece.span.valid⟩) := by
  unfold Queried at queried
  exact queried

/-- The SAME two stored children of the actual original split retain their original complete source factories. -/
theorem built_children_queried (piece : Piece data actual accuracy) (queried : piece.Queried)
    (child : Piece data actual accuracy.quarter)
    (member : child ∈ piece.children (Split.build piece.cell piece.within)) : child.Queried := by
  cases member with
  | head =>
      unfold Queried at queried ⊢
      exact queried
  | tail _ member =>
      cases member with
      | head =>
          unfold Queried
          rfl
      | tail _ impossible => nomatch impossible

end Piece

namespace Steps

/-- Original built midpoint steps propagate source receipts through their SAME retained ordered children. -/
theorem built_children_queried (parents : List (Piece data actual accuracy))
    (queried : ∀ parent ∈ parents, parent.Queried) :
    ∀ child ∈ (build parents).children, child.Queried := by
  induction parents with
  | nil => intro child impossible; nomatch impossible
  | cons parent parents retained =>
      intro child member
      change child ∈ parent.children (Split.build parent.cell parent.within) ++ (build parents).children at member
      cases Membership.mem_append.mp member with
      | inl first => exact parent.built_children_queried (queried parent (List.Mem.head parents)) child first
      | inr last => exact retained (fun entry present => queried entry (List.Mem.tail parent present)) child last

end Steps

namespace Piece

/-- Every complete source in the original layerAt result retains its actual initial-or-midpoint query receipt.

The initial factory receipt is supplied before refinement. Structural
induction follows the exact original layer and its actual built midpoint
steps. This theorem is erased proof evidence; it performs no time query.
-/
theorem layerAt_queried (initial : Piece data actual accuracy) (queried : initial.Queried) :
    (depth : Nat) → ∀ piece ∈ (initial.layerAt depth).pieces, piece.Queried
  | 0 => by
      intro piece member
      change piece ∈ [initial] at member
      have same := Membership.mem_singleton.mp member
      cases same
      exact queried
  | depth + 1 => by
      change ∀ piece ∈ (Steps.build (initial.layerAt depth).pieces).children, piece.Queried
      exact Steps.built_children_queried (initial.layerAt depth).pieces (initial.layerAt_queried queried depth)

end Piece

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement

end
