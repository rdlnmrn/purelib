module

public import Purelib.Riemann.Paths.PreparedTraceEdges
public import Purelib.Riemann.Paths.OwnerTracePath
public import Purelib.Riemann.Integration.PreparedConstantModels.Query
public import Purelib.Riemann.Readings.UniformPreparedRequests.Query
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Interval.ConvexCombination
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Tactic.Ring

/-! # Query-endpoint links inside one retained accepted moving trace edge

The same original request-fit bounds pay every ordered subinterval. Both
supplied query Owners refine its original cached prepared-source box. New
residual tails and one variation polynomial certify a link between those
exact Owners; no prepared query, step, path or continuation is replayed.
-/

public section

namespace Purelib.Riemann.Paths.PreparedTraceEdges.PreparedTraceBudget

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint StepRequest CachedSource parameterAt)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerTail ownerName)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerLink OwnerPath)
open Purelib.Riemann.RootContinuation.SquareRootTrace (EdgeData)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter_heq)

variable {polynomial : CoefficientPolynomial} {ambient : Box}
variable {start finish : Canonical} {segment : ClearSegment polynomial ambient start finish}
variable {first last current : Endpoint} {inherited : Owner (polynomial.eval (segment.pointAt current.parameter))}
variable {request : StepRequest} {cached : CachedSource segment current inherited request}

/-- Affine interpolation between two original segment parameters is the same physical chord. -/
private theorem interpolate_point (segment : ClearSegment polynomial ambient start finish)
    (lower upper time : Fraction.Rational) :
    Geometry.Rational.Affine.line (segment.pointAt lower) (segment.pointAt upper - segment.pointAt lower) time =
      segment.pointAt (lower + time * (upper - lower)) := by
  apply Basic.ext <;>
    simp only [Geometry.Rational.Affine.line, ClearSegment.pointAt, Scale.scale_re, Scale.scale_im,
      Cast.ofCoordinate_re, Cast.ofCoordinate_im, Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im,
      Basic.mul_re, Basic.mul_im] <;> ring1

/-- Construct a new certified link inside the SAME original prepared box and paid accepted interval.

The input Owners and their actual box-refinement certificates remain
unchanged. Two original residual tails and the new chord variation are
constructed once. Original request-fit bounds pay root displacement and
polynomial movement; no signed relation or new clearance is a premise.
-/
def linkWithin (budget : PreparedTraceBudget segment first last) (within : segment.WithinAmbient)
    (diameter : request.rootDiameter ≤ budget.rootDiameter)
    (movement : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter ≤
      budget.movementBudget)
    (lower upper : Endpoint) (firstLower : current.parameter ≤ lower.parameter)
    (ordered : lower.parameter ≤ upper.parameter) (upperLast : upper.parameter ≤ request.endpoint.parameter)
    (left : Owner (polynomial.eval (segment.pointAt lower.parameter)))
    (right : Owner (polynomial.eval (segment.pointAt upper.parameter)))
    (leftRefines : left.track.initial.box.Refines cached.preparedOwner.track.initial.box)
    (rightRefines : right.track.initial.box.Refines cached.preparedOwner.track.initial.box) :
    OwnerLink polynomial (segment.pointAt lower.parameter) (segment.pointAt upper.parameter) left right :=
  let leftTail := OwnerTail.acquire left
  let rightTail := OwnerTail.acquire right
  let base := segment.pointAt lower.parameter
  let finish := segment.pointAt upper.parameter
  let variation := (Substitution.Affine.composeLine polynomial base (finish - base) -
    constant (polynomial.eval base)).normalize
  { leftTail := leftTail
    rightTail := rightTail
    leftIndex := leftTail.first
    rightIndex := rightTail.first
    left_ge := le_rfl
    right_ge := le_rfl
    realize := fun source target _ _ => by
      have lowerBound : budget.lower ≤ source.norm := by
        rewrite [source.norm_eq, source.value_eq]
        exact budget.root_lower lower.parameter lower.inside left source.index
      have sourceInside := left.certificate_candidate_in_initial_box left.parameterNonzero leftTail.state
        source.possible
      have targetInside := right.certificate_candidate_in_initial_box right.parameterNonzero rightTail.state
        target.possible
      have diagonal : cached.preparedOwner.track.initial.box.diagonalSq ≤ budget.rootDiameter := by
        rewrite [cached.preparedOwner_eq]
        exact (PreparedSheetContinuation.prepared_diagonal_lt segment current inherited request).le.trans diameter
      have distance : normSq (target.value - source.value) ≤ source.norm / 1024 := by
        have bounded := (cached.preparedOwner.track.initial.box.normSq_sub_le_diagonalSq
          (rightRefines.contains targetInside) (leftRefines.contains sourceInside)).trans diagonal
        rewrite [budget.rootDiameter_eq, Norm.Basic.normSq_eq_canonical] at bounded
        exact bounded.trans (div_1024_mono lowerBound)
      let data : EdgeData polynomial source.value target.value base finish :=
        { rootNorm := source.norm
          rootNorm_eq := source.norm_eq
          distance := normSq (target.value - source.value)
          distance_eq := rfl
          residual := source.residualNorm
          residual_eq := source.residualNorm_eq
          variation := variation
          variation_eq := by
            intro time
            rewrite [eval_normalize, eval_sub, eval_constant, Substitution.Affine.eval_composeLine]
            rfl
          movementBound := budget.movementBudget
          movementBound_valid := by
            intro time inside
            rewrite [eval_normalize, eval_sub, eval_constant, Substitution.Affine.eval_composeLine]
            change normSq (polynomial.eval (Geometry.Rational.Affine.line base (finish - base) time) -
              polynomial.eval base) ≤ budget.movementBudget
            rewrite [interpolate_point]
            have between := Geometry.Rational.Box.coordinate_between
              (⟨Fraction.Order.Basic.le_refl _, ordered⟩ :
                lower.parameter ≤ lower.parameter ∧ lower.parameter ≤ upper.parameter)
              (⟨ordered, Fraction.Order.Basic.le_refl _⟩ :
                lower.parameter ≤ upper.parameter ∧ upper.parameter ≤ upper.parameter) inside
            have pointInside : 0 ≤ lower.parameter + time * (upper.parameter - lower.parameter) ∧
                lower.parameter + time * (upper.parameter - lower.parameter) ≤ 1 :=
              ⟨lower.inside.1.trans between.1, between.2.trans upper.inside.2⟩
            have evaluation := ClearSheetContinuation.evaluation_variation_le segment within lower.parameter
              (lower.parameter + time * (upper.parameter - lower.parameter)) lower.inside pointInside
            rewrite [Norm.Basic.normSq_eq_canonical] at evaluation
            have reversed : normSq (polynomial.eval
                (segment.pointAt (lower.parameter + time * (upper.parameter - lower.parameter))) -
                polynomial.eval (segment.pointAt lower.parameter)) =
                normSq (polynomial.eval (segment.pointAt lower.parameter) - polynomial.eval
                  (segment.pointAt (lower.parameter + time * (upper.parameter - lower.parameter)))) := by
              simp only [normSq, Basic.sub_re, Basic.sub_im]
              ring1
            rewrite [reversed]
            exact evaluation.trans
              ((ClearSheetContinuation.variationBound_le_of_subinterval segment firstLower between.1
                (between.2.trans upperLast)).trans movement) }
      refine ⟨data, budget.lower_positive.trans_le lowerBound, distance, source.residual_small, ?_⟩
      change budget.movementBudget ≤ source.norm ^ 2 / 1024
      rewrite [budget.movementBudget_eq]
      exact div_1024_mono (Fraction.Order.Arithmetic.pow_le_pow_direct budget.lower_positive.le lowerBound 2) }

/-- The two actual retained queries determine an oriented crop path inside their SAME original accepted parent.

The original budget pays the whole parent interval, so the derived scalar
subinterval incidence suffices. Nominal physical-point transports retain
both complete supplied query Owners; no query or parent is reconstructed.
-/
def queryPath {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    (parent : PreparedEdge curve differential) {first last : Endpoint}
    (budget : PreparedTraceBudget parent.segment first last)
    (diameter : parent.request.rootDiameter ≤ budget.rootDiameter)
    (movement : ClearSheetContinuation.variationBound parent.segment parent.left.parameter
      parent.request.endpoint.parameter ≤ budget.movementBudget)
    (lower upper : Fraction.Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1)
    (upperInside : 0 ≤ upper ∧ upper ≤ 1) (ordered : lower ≤ upper)
    (source : PreparedEdge.Query parent lower lowerInside) (target : PreparedEdge.Query parent upper upperInside) :
    OwnerPath curve.polynomial (parent.point lower) source.owner (parent.point upper) target.owner :=
  let left : Endpoint := ⟨parameterAt parent.left parent.request lower,
    PreparedSheetContinuation.parameterAt_inside parent.left parent.request parent.ordered lower lowerInside⟩
  let right : Endpoint := ⟨parameterAt parent.left parent.request upper,
    PreparedSheetContinuation.parameterAt_inside parent.left parent.request parent.ordered upper upperInside⟩
  have firstLeft := (PreparedSheetContinuation.parameterAt_between parent.left parent.request parent.ordered
    lower lowerInside).1
  have rightLast := (PreparedSheetContinuation.parameterAt_between parent.left parent.request parent.ordered
    upper upperInside).2
  have endpoints : left.parameter ≤ right.parameter := by
    change parameterAt parent.left parent.request lower ≤ parameterAt parent.left parent.request upper
    rewrite [PreparedSheetContinuation.parameterAt_eq_affine, PreparedSheetContinuation.parameterAt_eq_affine]
    exact Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl parent.left.parameter)
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct ordered
        (Fraction.Order.Arithmetic.sub_nonneg_direct parent.ordered))
  let link := linkWithin (cached := parent.cached) budget parent.within diameter movement left right
    firstLeft endpoints rightLast source.direct target.direct source.direct_refines target.direct_refines
  let direct : OwnerPath curve.polynomial (parent.segment.pointAt left.parameter) source.direct
      (parent.segment.pointAt right.parameter) target.direct :=
    .cons link (.nil (parent.segment.pointAt right.parameter) target.direct)
  have leftPoint : parent.segment.pointAt left.parameter = parent.point lower :=
    PreparedSheetContinuation.pointAt_parameterAt parent.segment parent.within parent.left parent.request lower
  have rightPoint : parent.segment.pointAt right.parameter = parent.point upper :=
    PreparedSheetContinuation.pointAt_parameterAt parent.segment parent.within parent.left parent.request upper
  direct.castEndpoints leftPoint rightPoint
    (castOwnerParameter_heq (parent.directQueryParameter_eq lower) source.direct).symm
    (castOwnerParameter_heq (parent.directQueryParameter_eq upper) target.direct).symm

/-- The crop keeps one ordered target occurrence even when the supplied fractions or physical points coincide. -/
theorem queryPath_vertices {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus} (parent : PreparedEdge curve differential) {first last : Endpoint}
    (budget : PreparedTraceBudget parent.segment first last)
    (diameter : parent.request.rootDiameter ≤ budget.rootDiameter)
    (movement : ClearSheetContinuation.variationBound parent.segment parent.left.parameter
      parent.request.endpoint.parameter ≤ budget.movementBudget)
    (lower upper : Fraction.Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1)
    (upperInside : 0 ≤ upper ∧ upper ≤ 1) (ordered : lower ≤ upper)
    (source : PreparedEdge.Query parent lower lowerInside) (target : PreparedEdge.Query parent upper upperInside) :
    (queryPath parent budget diameter movement lower upper lowerInside upperInside ordered source target).vertices =
      [parent.point upper] := by
  unfold queryPath
  rewrite [OwnerPath.castEndpoints_vertices]
  exact congrArg (fun point : Canonical => [point])
    (PreparedSheetContinuation.pointAt_parameterAt parent.segment parent.within parent.left parent.request upper)

/-- Construct the crop once on two actual Queries and derive both unchanged Point comparisons from their LocalRequest.

The original query refinements and Point seed refinements pay the signed
endpoint relations. Both Point Owners remain distinct from the query
Owners. No endpoint relation, primitive normalization or new query/Point
execution is a premise or performed by this operation.
-/
def queryPoints {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {target : Fraction.Rational} (parent : CenteredEdge curve differential) {first last : Endpoint}
    (budget : PreparedTraceBudget parent.edge.segment first last)
    (diameter : parent.edge.request.rootDiameter ≤ budget.rootDiameter)
    (movement : ClearSheetContinuation.variationBound parent.edge.segment parent.edge.left.parameter
      parent.edge.request.endpoint.parameter ≤ budget.movementBudget)
    (lower upper : Fraction.Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1)
    (upperInside : 0 ≤ upper ∧ upper ≤ 1) (ordered : lower ≤ upper)
    (source : PreparedEdge.Query parent.edge lower lowerInside)
    (finish : PreparedEdge.Query parent.edge upper upperInside)
    (request : LocalRequest parent count target)
    (sourceSample : ContinuedNeighborhood.Point request.neighborhood (parent.edge.point lower))
    (finishSample : ContinuedNeighborhood.Point request.neighborhood (parent.edge.point upper)) :
    OwnerPath curve.polynomial (parent.edge.point lower) source.owner (parent.edge.point upper) finish.owner ×
      NamedEquivalent (ownerName source.owner) sourceSample.certificate.value.name ×
      NamedEquivalent (ownerName finish.owner) finishSample.certificate.value.name :=
  let path := queryPath parent.edge budget diameter movement lower upper lowerInside upperInside ordered source finish
  let sourceEquivalent := NamedEquivalent.transport source.name_eq rfl
    (request.retainedQueryEquivalent lower lowerInside source rfl (request.point_inside lowerInside) sourceSample)
  let finishEquivalent := NamedEquivalent.transport finish.name_eq rfl
    (request.retainedQueryEquivalent upper upperInside finish rfl (request.point_inside upperInside) finishSample)
  ⟨path, sourceEquivalent, finishEquivalent⟩

end Purelib.Riemann.Paths.PreparedTraceEdges.PreparedTraceBudget

end
