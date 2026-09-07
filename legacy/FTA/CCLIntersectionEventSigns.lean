import FTA.CCLIntersectionPartition

/-!
# Signs of coprime conditions at CCL intersection events

A first-member Sturm leaf represents an algebraic parameter event by a
count-one rational interval, not by an assumed real root.  To interpret the
other closed box conditions at that event, refine the count-one transducer
once to a common explicit width.  The event polynomial then has opposite
endpoint signs, while every displayed coprime condition has a certified
constant strict sign on the same refined interval.  Exact evaluation at the
rational midpoint therefore decides the sign of every nonvanishing condition
at the algebraic event without selecting or completing a real value.
-/

namespace FTA
namespace CCLIntersectionEventSigns

open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.DenseSquarefree
open FTA.DenseDerivative
open FTA.Maximality
open FTA.RationalPolynomialBounds
open FTA.Sturm
open FTA.SturmTransducer

abbrev RatPolynomial := DensePolynomial ℚ
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

namespace FirstMemberCellCertificate

/-- The oriented first-member certificate really has opposite endpoint
signs.  This fact is deliberately exposed separately from its Cauchy-index
contribution because it drives sign determination for coprime conditions. -/
theorem endpoint_mul_neg {p : RatPolynomial} {interval : RationalInterval}
    (certificate : FirstMemberCellCertificate p interval) :
    p.eval interval.lower * p.eval interval.upper < 0 := by
  rcases mul_neg_iff.mp certificate.lowerOpposite with lower | lower
  · rcases mul_pos_iff.mp certificate.upperAligned with upper | upper
    · exact (not_lt_of_ge upper.2.le lower.2).elim
    · exact mul_neg_of_pos_of_neg lower.1 upper.1
  · rcases mul_pos_iff.mp certificate.upperAligned with upper | upper
    · exact mul_neg_of_neg_of_pos lower.1 upper.1
    · exact (not_lt_of_ge lower.2.le upper.2).elim

end FirstMemberCellCertificate

/-- A locally classified squarefree cell with doubled count two is an
oriented first-member crossing.  All other executable classifier branches
carry an exact zero-count certificate. -/
theorem endpoint_mul_neg_of_classified_count_eq_two
    {p : RatPolynomial} {input : SquarefreeInput p}
    {interval : RationalInterval} {proper : interval.Proper}
    {lowerClear : p.eval interval.lower ≠ 0}
    {upperClear : p.eval interval.upper ≠ 0}
    {partition : EventPartition p interval}
    (classified : classifiedEventLeaf? input interval proper lowerClear
      upperClear = some partition)
    (countTwo : sturmRootCount2 p interval.lower interval.upper = 2) :
    p.eval interval.lower * p.eval interval.upper < 0 := by
  simp only [classifiedEventLeaf?] at classified
  split at classified
  · rename_i first _firstResult
    exact
      FTA.CCLIntersectionEventSigns.FirstMemberCellCertificate.endpoint_mul_neg
        first.first
  · split at classified
    · rename_i noEvent _noEventResult
      have countZero := noEvent.count_eq_zero
      omega
    · split at classified
      · rename_i stable _stableResult
        have countZero := stable.sturmRootCount2_eq_zero
        omega
      · split at classified
        · rename_i interior _interiorResult
          have countZero := interior.sturmRootCount2_eq_zero
          omega
        · contradiction

/-- A locally classified count-one cell also fixes the orientation of its
lower endpoint against the squarefree event derivative.  This form is more
useful than endpoint crossing when comparing the lower endpoints of two
independent refinements of the same isolated event. -/
theorem lower_derivative_mul_neg_of_classified_count_eq_two
    {p : RatPolynomial} {input : SquarefreeInput p}
    {interval : RationalInterval} {proper : interval.Proper}
    {lowerClear : p.eval interval.lower ≠ 0}
    {upperClear : p.eval interval.upper ≠ 0}
    {partition : EventPartition p interval}
    (classified : classifiedEventLeaf? input interval proper lowerClear
      upperClear = some partition)
    (countTwo : sturmRootCount2 p interval.lower interval.upper = 2) :
    p.eval interval.lower * (derivative p).eval interval.lower < 0 := by
  simp only [classifiedEventLeaf?] at classified
  split at classified
  · rename_i first _firstResult
    exact first.first.lower_derivative_mul_neg
  · split at classified
    · rename_i noEvent _noEventResult
      have countZero := noEvent.count_eq_zero
      omega
    · split at classified
      · rename_i stable _stableResult
        have countZero := stable.sturmRootCount2_eq_zero
        omega
      · split at classified
        · rename_i interior _interiorResult
          have countZero := interior.sturmRootCount2_eq_zero
          omega
        · contradiction

/-- Any count-one refinement below the computed local-classifier width has
opposite endpoint signs. -/
theorem endpoint_mul_neg_of_countOne_refined_width
    {p : RatPolynomial} (input : SquarefreeInput p)
    (root child : RationalInterval) (refines : child.Refines root)
    (proper : child.Proper) (lowerClear : p.eval child.lower ≠ 0)
    (upperClear : p.eval child.upper ≠ 0)
    (countOne : sturmRootCount2 p child.lower child.upper = 2)
    (width : child.width < ambientEventClassifierWidthResolution input root) :
    p.eval child.lower * p.eval child.upper < 0 := by
  let result := classifiedEventLeaf?_succeeds_of_refined_width input root child
    refines proper lowerClear upperClear width
  exact endpoint_mul_neg_of_classified_count_eq_two result.2 countOne

/-- Uniform-width specialization of the lower-endpoint orientation theorem. -/
theorem lower_derivative_mul_neg_of_countOne_refined_width
    {p : RatPolynomial} (input : SquarefreeInput p)
    (root child : RationalInterval) (refines : child.Refines root)
    (proper : child.Proper) (lowerClear : p.eval child.lower ≠ 0)
    (upperClear : p.eval child.upper ≠ 0)
    (countOne : sturmRootCount2 p child.lower child.upper = 2)
    (width : child.width < ambientEventClassifierWidthResolution input root) :
    p.eval child.lower * (derivative p).eval child.lower < 0 := by
  let result := classifiedEventLeaf?_succeeds_of_refined_width input root child
    refines proper lowerClear upperClear width
  exact lower_derivative_mul_neg_of_classified_count_eq_two result.2 countOne

/-- Values opposite to two same-sign orienting values have the same strict
sign.  This elementary rational transfer keeps the event comparison below
entirely multiplicative, with no sign case split. -/
theorem mul_pos_of_mul_neg_of_orienters_mul_pos
    {a b x y : ℚ} (hax : a * x < 0) (hby : b * y < 0)
    (hxy : 0 < x * y) :
    0 < a * b := by
  have hxa : 0 < (-x) * a := by
    simpa [mul_comm] using (neg_pos.mpr hax)
  have hxyNeg : 0 < (-x) * (-y) := by
    simpa using hxy
  have hay : 0 < a * (-y) :=
    mul_pos_of_mul_pos_left hxa hxyNeg
  have hya : 0 < (-y) * a := by
    simpa [mul_comm] using hay
  have hyb : 0 < (-y) * b := by
    simpa [mul_comm] using (neg_pos.mpr hby)
  exact mul_pos_of_mul_pos_left hya hyb

/-- The lower rational representatives of any two sufficiently narrow
count-one refinements of one oriented squarefree event lie on the same strict
side of that event.  No algebraic root or completed real parameter is used. -/
theorem lower_evals_mul_pos_of_countOne_refinements
    {p : RatPolynomial} (input : SquarefreeInput p)
    (root : RationalInterval)
    (derivativeSign : IntervalSignCertificate (derivative p)
      root.lower root.upper)
    (left right : CountOneInterval p)
    (leftRefines : left.interval.Refines root)
    (rightRefines : right.interval.Refines root)
    (leftWidth : left.interval.width <
      ambientEventClassifierWidthResolution input root)
    (rightWidth : right.interval.width <
      ambientEventClassifierWidthResolution input root) :
    0 < p.eval left.interval.lower * p.eval right.interval.lower := by
  have leftOrientation :=
    lower_derivative_mul_neg_of_countOne_refined_width input root left.interval
      leftRefines left.proper left.lowerClear left.upperClear left.countOne
      leftWidth
  have rightOrientation :=
    lower_derivative_mul_neg_of_countOne_refined_width input root right.interval
      rightRefines right.proper right.lowerClear right.upperClear right.countOne
      rightWidth
  have derivativeAligned := derivativeSign.eval_mul_pos_between
    leftRefines.1 (left.proper.le.trans leftRefines.2)
    rightRefines.1 (right.proper.le.trans rightRefines.2)
  exact mul_pos_of_mul_neg_of_orienters_mul_pos leftOrientation
    rightOrientation derivativeAligned

/-- One additional polynomial whose sign is requested at an event of `p`.
The Bézout certificate is executable evidence that it cannot vanish at the
same algebraic event. -/
structure CoprimeCondition (p : RatPolynomial) where
  polynomial : RatPolynomial
  coprime : CoprimeCertificate p polynomial

/-- Positive ambient radius resolving every displayed coprime condition at
once.  The positive default handles an empty condition list. -/
def commonCoprimeRadius {p : RatPolynomial}
    (conditions : List (CoprimeCondition p)) (root : RationalInterval) : ℚ :=
  positiveMinimum (conditions.map fun condition =>
    ambientCoprimeCellRadius condition.coprime
      (intervalMagnitude root.lower root.upper))

theorem commonCoprimeRadius_pos {p : RatPolynomial}
    (conditions : List (CoprimeCondition p)) (root : RationalInterval) :
    0 < commonCoprimeRadius conditions root := by
  apply positiveMinimum_pos
  intro radius member
  rw [List.mem_map] at member
  rcases member with ⟨condition, _conditionMember, rfl⟩
  exact ambientCoprimeCellRadius_pos condition.coprime
    (intervalMagnitude_pos root.lower root.upper).le

theorem commonCoprimeRadius_le {p : RatPolynomial}
    {conditions : List (CoprimeCondition p)} {condition : CoprimeCondition p}
    (member : condition ∈ conditions) (root : RationalInterval) :
    commonCoprimeRadius conditions root ≤
      ambientCoprimeCellRadius condition.coprime
        (intervalMagnitude root.lower root.upper) := by
  apply positiveMinimum_le_of_mem
  exact List.mem_map.mpr ⟨condition, member, rfl⟩

/-- One width simultaneously resolving the event orientation and all
coprime condition signs. -/
def eventSignResolution {p : RatPolynomial} (input : SquarefreeInput p)
    (conditions : List (CoprimeCondition p)) (root : RationalInterval) : ℚ :=
  min (ambientEventClassifierWidthResolution input root)
    (2 * commonCoprimeRadius conditions root)

theorem eventSignResolution_pos {p : RatPolynomial}
    (input : SquarefreeInput p) (conditions : List (CoprimeCondition p))
    (root : RationalInterval) :
    0 < eventSignResolution input conditions root := by
  exact lt_min (ambientEventClassifierWidthResolution_pos input root)
    (mul_pos (by norm_num) (commonCoprimeRadius_pos conditions root))

/-- Proof-bearing result of the bounded shared refinement.  All condition
certificates refer to the same count-one interval, so their signs may be
combined by a finite Boolean table. -/
structure CommonEventSigns {p : RatPolynomial} (input : SquarefreeInput p)
    (conditions : List (CoprimeCondition p))
    (parent : CountOneInterval p) where
  refined : CountOneInterval p
  refines : refined.interval.Refines parent.interval
  crossing : p.eval refined.interval.lower * p.eval refined.interval.upper < 0
  signs : ∀ condition ∈ conditions,
    IntervalSignCertificate condition.polynomial
      refined.interval.lower refined.interval.upper

/-- Execute the common count-one refinement and construct every coprime sign
certificate.  The only recursion is the already bounded transducer call. -/
def computeCommonEventSigns {p : RatPolynomial} (input : SquarefreeInput p)
    (conditions : List (CoprimeCondition p))
    (parent : CountOneInterval p) :
    CommonEventSigns input conditions parent := by
  let resolution := eventSignResolution input conditions parent.interval
  have resolutionPositive : 0 < resolution :=
    eventSignResolution_pos input conditions parent.interval
  let requestedWidth := resolution / 2
  have requestedWidthPositive : 0 < requestedWidth := by
    dsimp only [requestedWidth]
    linarith
  let refined := runToWidth input (computedEventPartitionProgram input) parent
    requestedWidth requestedWidthPositive
  have refines : refined.interval.Refines parent.interval := by
    exact runToWidth_refines input (computedEventPartitionProgram input) parent
      requestedWidth requestedWidthPositive
  have widthLe : refined.interval.width ≤ requestedWidth := by
    exact runToWidth_le input (computedEventPartitionProgram input) parent
      requestedWidth requestedWidthPositive
  have widthResolution : refined.interval.width < resolution := by
    dsimp only [requestedWidth] at widthLe
    linarith
  have eventWidth : refined.interval.width <
      ambientEventClassifierWidthResolution input parent.interval :=
    widthResolution.trans_le (min_le_left _ _)
  have crossing : p.eval refined.interval.lower *
      p.eval refined.interval.upper < 0 :=
    endpoint_mul_neg_of_countOne_refined_width input parent.interval
      refined.interval refines refined.proper refined.lowerClear
      refined.upperClear refined.countOne eventWidth
  refine
    { refined
      refines
      crossing
      signs := ?_ }
  intro condition member
  have commonWidth : refined.interval.width <
      2 * commonCoprimeRadius conditions parent.interval :=
    widthResolution.trans_le (min_le_right _ _)
  have midpointRadius : intervalRadius refined.interval.lower
      refined.interval.upper
      (midpoint refined.interval.lower refined.interval.upper) <
      commonCoprimeRadius conditions parent.interval := by
    rw [refined.interval.midpointRadius_eq_half_width refined.proper]
    linarith
  have ambientRadius : intervalRadius refined.interval.lower
      refined.interval.upper
      (midpoint refined.interval.lower refined.interval.upper) <
      ambientCoprimeCellRadius condition.coprime
        (intervalMagnitude parent.interval.lower parent.interval.upper) :=
    midpointRadius.trans_le
      (commonCoprimeRadius_le member parent.interval)
  have magnitude : intervalMagnitude refined.interval.lower
      refined.interval.upper ≤
      intervalMagnitude parent.interval.lower parent.interval.upper :=
    refined.interval.intervalMagnitude_le_of_refines refines refined.proper
  have cellRadius : intervalRadius refined.interval.lower
      refined.interval.upper
      (midpoint refined.interval.lower refined.interval.upper) <
      coprimeCellRadius condition.coprime refined.interval.lower
        refined.interval.upper :=
    ambientRadius.trans_le
      (ambientCoprimeCellRadius_le_cellRadius condition.coprime magnitude)
  exact secondSignCertificateOfFirstEndpointCrossing condition.coprime
    refined.proper cellRadius crossing

/-- Executable nonnegative-sign bit for one condition on a common event
cell. -/
def CommonEventSigns.nonnegative {p : RatPolynomial}
    {input : SquarefreeInput p} {conditions : List (CoprimeCondition p)}
    {parent : CountOneInterval p}
    (result : CommonEventSigns input conditions parent)
    (condition : CoprimeCondition p) (member : condition ∈ conditions) : Bool :=
  decide (0 ≤ condition.polynomial.eval (result.signs condition member).sample)

private theorem nonneg_iff_of_mul_pos {a b : ℚ} (positive : 0 < a * b) :
    0 ≤ a ↔ 0 ≤ b := by
  rcases mul_pos_iff.mp positive with signs | signs
  · exact ⟨fun _ => signs.2.le, fun _ => signs.1.le⟩
  · constructor <;> intro nonnegative <;> linarith

/-- The computed bit is the closed sign of the condition at every rational
point of the refined event interval.  Because the condition is coprime to the
event polynomial, equality cannot occur there. -/
theorem CommonEventSigns.nonnegative_eq_true_iff
    {p : RatPolynomial} {input : SquarefreeInput p}
    {conditions : List (CoprimeCondition p)} {parent : CountOneInterval p}
    (result : CommonEventSigns input conditions parent)
    (condition : CoprimeCondition p) (member : condition ∈ conditions)
    {t : ℚ} (lower : result.refined.interval.lower ≤ t)
    (upper : t ≤ result.refined.interval.upper) :
    result.nonnegative condition member = true ↔
      0 ≤ condition.polynomial.eval t := by
  let certificate := result.signs condition member
  have sameSign := certificate.eval_mul_pos_between
    certificate.lowerLe certificate.leUpper lower upper
  rw [CommonEventSigns.nonnegative]
  simp only [decide_eq_true_eq]
  exact nonneg_iff_of_mul_pos sameSign

end CCLIntersectionEventSigns
end FTA
