module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance.Envelope.Numerator.Work
public import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
public import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Dyadic
public import Purelib.Data.Vector.Dependent
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Membership

/-! # Fixed original coarse envelopes before all finer six-row observations

The original dyadic midpoint tree stores one complete six-row numerator
cache at each original coarse left endpoint. A finite lookup reads the
actual stored leaf selected by a supplied chart time. The sum of all SAME
stored leaf costs bounds that leaf independently of every finer depth.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance.Envelope

namespace Numerators

open Purelib
open Purelib.Algebra
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Vector (DependentVector)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Riemann.Branches.ClearSheetContinuation
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}

/-- Six materialized original numerator caches at one retained original coarse source endpoint. -/
abbrev Leaf (reference : Endpoint) (regular : parameter ≠ criticalValue site) :=
  DependentVector (fun index : Fin 6 =>
    Numerator (quarter := quarter) (Specification.Table.forms parameter index) reference.parameter regular)

/-- Retained original dyadic coarse leaves, each containing its SAME six complete numerator folds.

Only the original midpoint depth is matched. The endpoint records are the
original dyadicTargets/dyadicEdges records; no geometric root preparation
or observations are acquired on these polynomial bounding envelopes.
-/
@[expose] def Cache (regular : parameter ≠ criticalValue site) : Nat → Endpoint → Endpoint → Type 1
  | 0, left, _ => Leaf (quarter := quarter) left regular
  | depth + 1, left, right =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
      Cache regular depth left middle × Cache regular depth middle right

/-- Compute each original coarse-envelope numerator once and retain all six exact original cache factories. -/
def build (regular : parameter ≠ criticalValue site) :
    (depth : Nat) → (left right : Endpoint) → Cache (quarter := quarter) regular depth left right
  | 0, left, _ =>
      DependentVector.ofFn (fun index =>
        Numerator.build (Specification.Table.forms parameter index) left.parameter regular)
  | depth + 1, left, right =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
      let first := build regular depth left middle
      let last := build regular depth middle right
      (first, last)

variable (data : (index : Fin 6) →
  Waist.Differential.Bounds.Data site parameter (Specification.Table.forms parameter index))

/-- Sum the actual fixed costs of the SAME six stored original caches at one coarse endpoint. -/
@[expose] def leafCost {reference : Endpoint} {regular : parameter ≠ criticalValue site}
    (leaf : Leaf (quarter := quarter) reference regular) : Fraction.Rational :=
  FiniteSum.Fin.sumFin (fun index => (leaf.get index).cost (data index))

/-- Every actual original coarse leaf has nonnegative total cost. -/
theorem leafCost_nonnegative {reference : Endpoint} {regular : parameter ≠ criticalValue site}
    (leaf : Leaf (quarter := quarter) reference regular) : 0 ≤ leafCost data leaf :=
  FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun index => (leaf.get index).cost_nonnegative (data index))

/-- Each stored original row cost lies below the SAME actual six-row leaf sum. -/
theorem cost_le_leafCost {reference : Endpoint} {regular : parameter ≠ criticalValue site}
    (leaf : Leaf (quarter := quarter) reference regular) (index : Fin 6) :
    (leaf.get index).cost (data index) ≤ leafCost data leaf :=
  FiniteSum.Rational.Order.weight_le_sum _ (fun entry => (leaf.get entry).cost_nonnegative (data entry)) index

/-- Sum the actual fixed costs of every original coarse leaf without inspecting a changing finer layer. -/
@[expose] def cost {regular : parameter ≠ criticalValue site} :
    (depth : Nat) → (left right : Endpoint) → Cache (quarter := quarter) regular depth left right → Fraction.Rational
  | 0, _, _, leaf => leafCost data leaf
  | depth + 1, left, right, retained =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
      cost depth left middle retained.1 + cost depth middle right retained.2

/-- All SAME retained original leaf costs have a nonnegative finite total. -/
theorem cost_nonnegative {regular : parameter ≠ criticalValue site} :
    (depth : Nat) → (left right : Endpoint) →
    (retained : Cache (quarter := quarter) regular depth left right) → 0 ≤ cost data depth left right retained
  | 0, _, _, leaf => leafCost_nonnegative data leaf
  | depth + 1, left, right, retained =>
      Fraction.Order.Arithmetic.add_le_add_direct
        (cost_nonnegative depth left _ retained.1) (cost_nonnegative depth _ right retained.2)

/-- One actual stored coarse leaf at the original dyadic edge containing the requested time.

The original cache remains an index. The result retains its selected exact
edge, SAME complete stored six-row leaf, original membership/interval
certificates, and the internally proved comparison to the total cache cost.
-/
@[expose] def Selected {regular : parameter ≠ criticalValue site} {depth : Nat} {left right : Endpoint}
    (retained : Cache (quarter := quarter) regular depth left right) (time : Fraction.Rational) : Type 1 :=
  Σ edge : ParameterEdge, { leaf : Leaf (quarter := quarter) edge.left regular //
    edge ∈ dyadicEdges depth left right ∧
      (edge.left.parameter ≤ time ∧ time ≤ edge.right.parameter) ∧
        leafCost data leaf ≤ cost data depth left right retained }

/-- Locate an original coarse interval and read its retained six-row cache without invoking a numerator factory. -/
def select {regular : parameter ≠ criticalValue site} :
    (depth : Nat) → (left right : Endpoint) → (retained : Cache (quarter := quarter) regular depth left right) →
    (time : Fraction.Rational) → (between : left.parameter ≤ time ∧ time ≤ right.parameter) →
      Selected data retained time
  | 0, left, right, leaf, _time, between =>
      ⟨⟨left, right⟩, leaf, List.Mem.head [], between, Fraction.Order.Basic.le_refl _⟩
  | depth + 1, left, right, retained, time, between =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
      if lower : time ≤ middle.parameter then
        let found := select depth left middle retained.1 time ⟨between.1, lower⟩
        ⟨found.1, found.2.1,
          Membership.mem_append.mpr (Or.inl found.2.2.1), found.2.2.2.1,
          found.2.2.2.2.trans (by
            have nonnegative := cost_nonnegative data depth middle right retained.2
            have enlarged := Fraction.Order.Arithmetic.add_le_add_direct
              (Fraction.Order.Basic.le_refl (cost data depth left middle retained.1)) nonnegative
            have rightZero : cost data depth left middle retained.1 + 0 =
                cost data depth left middle retained.1 :=
              (Fraction.Field.add_comm _ 0).trans (Fraction.Field.zero_add _)
            exact rightZero.symm.trans_le enlarged)⟩
      else
        let found := select depth middle right retained.2 time
          ⟨(Fraction.Order.Arithmetic.lt_of_not_ge_direct lower).1, between.2⟩
        ⟨found.1, found.2.1,
          Membership.mem_append.mpr (Or.inr found.2.2.1), found.2.2.2.1,
          found.2.2.2.2.trans (by
            have nonnegative := cost_nonnegative data depth left middle retained.1
            have enlarged := Fraction.Order.Arithmetic.add_le_add_direct nonnegative
              (Fraction.Order.Basic.le_refl (cost data depth middle right retained.2))
            exact (Fraction.Field.zero_add _).symm.trans_le enlarged)⟩

namespace Selected

variable {data}
variable {regular : parameter ≠ criticalValue site} {depth : Nat} {left right : Endpoint}
variable {retained : Cache (quarter := quarter) regular depth left right} {time : Fraction.Rational}
variable (selected : Selected data retained time)

/-- Read the identical complete original coarse six-row leaf selected from the retained cache. -/
@[expose] def leaf : Leaf (quarter := quarter) selected.1.left regular := selected.2.1

/-- The actual selected interval is an occurrence of the SAME original dyadic edge list. -/
theorem member : selected.1 ∈ dyadicEdges depth left right := selected.2.2.1

/-- The original requested time is between the SAME actual selected interval endpoints. -/
theorem between : selected.1.left.parameter ≤ time ∧ time ≤ selected.1.right.parameter := selected.2.2.2.1

/-- The actual selected original row cost is bounded by the SAME fixed total computed before finer observations. -/
theorem cost_le (index : Fin 6) :
    (selected.leaf.get index).cost (data index) ≤ cost data depth left right retained :=
  (cost_le_leafCost data selected.leaf index).trans selected.2.2.2.2

end Selected

end Numerators

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance.Envelope

end
