import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.ConditionalJensen

/-!
# Finite conditional Cauchy--Schwarz inequalities

Conditioning on one explicitly positive event produces another displayed
finite rational distribution.  Applying the root-free powered-L2 inequality
to that table gives conditional Cauchy--Schwarz without choosing square roots.
Centering the two observables gives the corresponding conditional covariance
bound.  The same eventwise calculation is exposed pointwise over a displayed
positive partition.
-/

namespace FiniteMeasure

namespace Distribution

/-- Root-free Cauchy--Schwarz inside one explicitly positive finite event. -/
theorem conditionalMean_mul_sq_le {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Coordinate) :
    distribution.conditionalMean event
          (fun item => left item * right item) ^ 2 ≤
      distribution.conditionalMean event (fun item => left item ^ 2) *
        distribution.conditionalMean event (fun item => right item ^ 2) := by
  have bounded := (distribution.conditioned event positive)
    |>.productExpectation_sq_le_poweredL2_mul left right
  change (distribution.conditioned event positive).expectation
        (fun item => left item * right item) ^ 2 ≤
      (distribution.conditioned event positive).expectation
          (fun item => left item ^ 2) *
        (distribution.conditioned event positive).expectation
          (fun item => right item ^ 2) at bounded
  rw [distribution.conditioned_expectation_eq_conditionalMean
      event positive (fun item => left item * right item),
    distribution.conditioned_expectation_eq_conditionalMean
      event positive (fun item => left item ^ 2),
    distribution.conditioned_expectation_eq_conditionalMean
      event positive (fun item => right item ^ 2)] at bounded
  exact bounded

/-- Exact rational covariance within one positive conditioning event. -/
def conditionalCovariance {α : Type} (distribution : Distribution α)
    (event : α → Bool) (left right : α → Coordinate) : Coordinate :=
  distribution.conditionalMean event fun item =>
    (left item - distribution.conditionalMean event left) *
      (right item - distribution.conditionalMean event right)

/-- Conditional covariance is the conditional product mean minus the product
of the two conditional means. -/
theorem conditionalCovariance_eq_product_sub_mul {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Coordinate) :
    distribution.conditionalCovariance event left right =
      distribution.conditionalMean event
          (fun item => left item * right item) -
        distribution.conditionalMean event left *
          distribution.conditionalMean event right := by
  unfold conditionalCovariance
  let leftMean := distribution.conditionalMean event left
  let rightMean := distribution.conditionalMean event right
  have expansion : distribution.conditionalMean event (fun item =>
      (left item - leftMean) * (right item - rightMean)) =
      distribution.conditionalMean event (fun item =>
        left item * right item - leftMean * right item -
          rightMean * left item + leftMean * rightMean) :=
    distribution.conditionalMean_congr event _ _ (fun item => by ring1)
  rw [expansion, distribution.conditionalMean_add,
    distribution.conditionalMean_sub, distribution.conditionalMean_sub,
    distribution.conditionalMean_scale,
    distribution.conditionalMean_scale,
    distribution.conditionalMean_constant event positive]
  dsimp only [leftMean, rightMean]
  ring1

/-- Root-free conditional covariance Cauchy--Schwarz. -/
theorem conditionalCovariance_sq_le_variance_mul {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Coordinate) :
    distribution.conditionalCovariance event left right ^ 2 ≤
      distribution.conditionalVariance event left *
        distribution.conditionalVariance event right := by
  exact distribution.conditionalMean_mul_sq_le event positive
    (fun item => left item - distribution.conditionalMean event left)
    (fun item => right item - distribution.conditionalMean event right)

end Distribution

namespace PositiveEventPartition

/-- Conditional Cauchy--Schwarz holds pointwise on every displayed atom of a
positive finite partition. -/
theorem conditionalExpectation_mul_sq_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Coordinate) (atom : Weighted α)
    (member : atom ∈ distribution.atoms) :
    partition.conditionalExpectation
          (fun item => left item * right item) atom.item ^ 2 ≤
      partition.conditionalExpectation
          (fun item => left item ^ 2) atom.item *
        partition.conditionalExpectation
          (fun item => right item ^ 2) atom.item := by
  rcases partition.toEventPartition.exists_selected_event atom member with
    ⟨event, eventMember, selected⟩
  rw [partition.conditionalExpectation_eq_conditionalMean_on_cell
      (fun item => left item * right item) event eventMember atom member
      selected,
    partition.conditionalExpectation_eq_conditionalMean_on_cell
      (fun item => left item ^ 2) event eventMember atom member selected,
    partition.conditionalExpectation_eq_conditionalMean_on_cell
      (fun item => right item ^ 2) event eventMember atom member selected]
  exact distribution.conditionalMean_mul_sq_le event
    (partition.positive event eventMember) left right

end PositiveEventPartition

end FiniteMeasure
