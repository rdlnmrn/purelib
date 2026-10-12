module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison
public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction
public import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Mathlib.Order.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRootOverlap

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

@[expose] public section

/-!
# Polynomial sheets along actual covered prepared chains

An inverse polynomial is aligned with an operational root if it agrees with
every sufficiently accurate local model of that occurrence. The finite
three-model cocycle propagates this property through each covered prepared
edge, using the edge's actual root queries. No new root is selected and no
sign-agreement hypothesis is needed at later vertices.
-/

section

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Riemann.Normalization.InverseModelOverlap (OverlapSample)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

namespace Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.Model

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Refine the original inverse-root model by the supplied index plus two, retaining the overlap-ready residual
threshold. -/
def overlapRefine {polynomial : Polynomial} {box : Box} (model : Model polynomial box) (index : Nat) :
    OverlapReady polynomial box :=
  ⟨model.refine (index + 2), by
    rw [Model.refine_bound]
    apply (quarterRadius_antitone model.bound_nonnegative (Nat.le_add_left 2 index)).trans
    rw [Geometric.Basic.quarterRadius_eq_mul_pow]
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct model.bound_small
      (by decide +kernel : (0 : Coordinate) ≤ (1 / 4) ^ 2)).trans
      (by decide +kernel : (1 / 16 : Coordinate) * (1 / 4) ^ 2 ≤ 1 / 256)⟩

end Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.Model

section
open Purelib.Data.Gaussian

namespace Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial

/-- Retain the original two model evaluations as an unflipped overlap sample using the supplied nearestness inequality.
-/
private def unflippedSample {polynomial : Polynomial} {leftBox rightBox : Box}
    (left : Model polynomial leftBox) (right : Model polynomial rightBox) (point : Gaussian)
    (nearest : Data.Gaussian.Norm.Basic.normSq (left.value.eval point - right.value.eval point) ≤
      Data.Gaussian.Norm.Basic.normSq
      (left.value.eval point + right.value.eval point)) :
    OverlapSample left right point :=
  ⟨left.value.eval point, rfl, right.value.eval point, rfl, ⟨false, right.value.eval point, rfl, by
    simpa only [Norm.Basic.normSq_eq_canonical] using nearest⟩⟩

/-- An unflipped overlap sample retains nearestness of the original evaluations.

The cached sign-adjusted value selects the unchanged right evaluation. Its
original value equations transport the retained quadrance comparison directly. -/
private theorem nearest_of_unflipped {polynomial : Polynomial} {leftBox rightBox : Box}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {point : Gaussian}
    (sample : OverlapSample left right point) (unflipped : sample.alignment.flip = false) :
    Data.Gaussian.Norm.Basic.normSq (left.value.eval point - right.value.eval point) ≤ Data.Gaussian.Norm.Basic.normSq
      (left.value.eval point + right.value.eval point) := by
  have nearest := sample.alignment.nearest
  rw [sample.alignment.value_eq, unflipped] at nearest
  rw [if_neg (show ¬(false = true) from fun impossible => by cases impossible)] at nearest
  simpa only [Norm.Basic.normSq_eq_canonical, sample.leftValue_eq, sample.rightValue_eq] using nearest

end Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial

end

section
open Purelib.Data.Gaussian

namespace Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial.OverlapReady

/-- Compose nearestness of three overlap-ready original model evaluations at the same retained point.

All three original boxes contain the point. The retained overlap cocycle identifies the direct flip with the two
supplied unflipped comparisons. -/
theorem nearest_trans
  {polynomial : Polynomial} {firstBox middleBox lastBox : Box}
    (first : OverlapReady polynomial firstBox) (middle : OverlapReady polynomial middleBox)
    (last : OverlapReady polynomial lastBox) {point : Gaussian}
    (firstInside : firstBox.Contains point) (middleInside : middleBox.Contains point) (lastInside : lastBox.Contains
      point)
    (firstMiddle : Data.Gaussian.Norm.Basic.normSq (first.model.value.eval point - middle.model.value.eval point) ≤
      Data.Gaussian.Norm.Basic.normSq (first.model.value.eval point + middle.model.value.eval point))
    (middleLast : Data.Gaussian.Norm.Basic.normSq (middle.model.value.eval point - last.model.value.eval point) ≤
      Data.Gaussian.Norm.Basic.normSq (middle.model.value.eval point + last.model.value.eval point)) :
    Data.Gaussian.Norm.Basic.normSq (first.model.value.eval point - last.model.value.eval point) ≤
      Data.Gaussian.Norm.Basic.normSq (first.model.value.eval point + last.model.value.eval point) := by
  let direct := OverlapSample.build first.model last.model point
  have cocycle := OverlapReady.cocycle first middle last firstInside middleInside lastInside
    (Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.unflippedSample first.model middle.model point
      firstMiddle)
    (Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.unflippedSample middle.model last.model point
      middleLast) direct
  exact Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.nearest_of_unflipped direct cocycle

end Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial.OverlapReady

namespace Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.Model

/-- Nearestness of two original inverse-root models at a common segment start persists to its retained finish.

Both endpoints belong to both original model boxes; the retained edge transition preserves the unflipped start sample
throughout the exact segment. -/
theorem nearest_finish {polynomial : Polynomial} {leftBox rightBox : Box}
    (left : Model polynomial leftBox) (right : Model polynomial rightBox) {start finish : Gaussian}
    (leftStart : leftBox.Contains start) (leftFinish : leftBox.Contains finish)
    (rightStart : rightBox.Contains start) (rightFinish : rightBox.Contains finish)
    (nearest : Data.Gaussian.Norm.Basic.normSq (left.value.eval start - right.value.eval start) ≤
      Data.Gaussian.Norm.Basic.normSq
      (left.value.eval start + right.value.eval start)) :
    Data.Gaussian.Norm.Basic.normSq (left.value.eval finish - right.value.eval finish) ≤ Data.Gaussian.Norm.Basic.normSq
      (left.value.eval finish + right.value.eval finish) := by
  let edge : EdgeTransition left right start finish :=
    ⟨leftStart, leftFinish, rightStart, rightFinish,
      PreparedPolynomialSheetPropagation.InverseRootPolynomial.unflippedSample left right start nearest⟩
  exact PreparedPolynomialSheetPropagation.InverseRootPolynomial.nearest_of_unflipped (OverlapSample.build left right
    finish) edge.flip_eq_finish.symm

end Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.Model

end

namespace Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
/-- An overlap-ready model agrees in sign with every retained continued root reading equivalent to the specified
original root name.

The predicate retains the point, model and original name. Each comparison uses the supplied continued neighborhood and
point owner with its exact indexed refinement plus two. -/
def RootAligned {polynomial : Polynomial} {box : Box} (model : OverlapReady polynomial box)
    (point : Gaussian) (root : Name.Basic.Named) : Prop :=
  ∀ {count : Nat} (patch : ContinuedNeighborhood polynomial count) (_inside : patch.box.Contains point)
    (sample : ContinuedNeighborhood.Point patch point)
    (_roots : Equivalence.NamedEquivalent root sample.certificate.value.name) (index : Nat),
    Data.Gaussian.Norm.Basic.normSq (model.model.value.eval point - (patch.base.refine (index + 2)).value.eval point) ≤
      Data.Gaussian.Norm.Basic.normSq (model.model.value.eval point + (patch.base.refine (index + 2)).value.eval point)

end Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial

section

variable {polynomial : Polynomial} {box : Box} {model : OverlapReady polynomial box}
  {point : Gaussian} {first last : Purelib.Approximation.Gaussian.Name.Basic.Named}

namespace Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.RootAligned

open Purelib.Approximation.Gaussian in
/-- Transport retained model alignment along an operational equivalence of the original root names. -/
theorem changeName (aligned : InverseRootPolynomial.RootAligned model point first) (equivalent :
  Equivalence.NamedEquivalent first last) :
    Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.RootAligned model point last :=
  fun patch inside sample roots index => aligned patch inside sample (equivalent.trans roots) index

end Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.RootAligned

end

end

section

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial (RootAligned)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named LiftedPoint)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {box : Box} {model : OverlapReady curve.polynomial box}

namespace Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation

open Purelib.Data.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Normalization in
/-- Propagate an original model's root alignment across a covered prepared edge.

Both original edge endpoints lie in the model box, and the retained prepared patch covers the finish. Edge sign
constancy and equivalent point-root readings preserve alignment with the exact finish query. -/
theorem advance {parent : CenteredEdge curve differential} {count : Nat}
    (patch : PreparedPatch parent) (covered : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (firstInside : box.Contains (parent.edge.point 0)) (lastInside : box.Contains (parent.edge.point 1))
    (aligned : RootAligned model (parent.edge.point 0) (parent.edge.rootName 0 parent.edge.baseInside)) :
    RootAligned model (parent.edge.point 1) (parent.edge.rootName 1 (by decide)) := by
  intro otherCount other otherInside sample roots index
  let middle := patch.neighborhood count
  let first := ContinuedNeighborhood.Point.acquire middle (parent.edge.point 0) (patch.start_inside count)
  let last := ContinuedNeighborhood.Point.acquire middle (parent.edge.point 1) covered
  have initial := aligned middle (patch.start_inside count) first
    (patch.point_equivalent count 0 parent.edge.baseInside (patch.start_inside count) first) 0
  have transported := (InverseRootPolynomial.Model.nearest_finish model.model)
    (middle.base.refine 2) firstInside lastInside
    (middle.box_refines.contains (patch.start_inside count)) (middle.box_refines.contains covered) initial
  have next := last.equivalent_nearest sample covered otherInside
    ((patch.point_equivalent count 1 (by decide) covered last).symm.trans roots) 2 (index + 2)
  apply model.nearest_trans ((InverseRootPolynomial.Model.overlapRefine
    middle.base.model) 0) ((InverseRootPolynomial.Model.overlapRefine
    other.base.model) index)
    lastInside (middle.box_refines.contains covered) (other.box_refines.contains otherInside) transported
  simpa only [Norm.Basic.normSq_eq_canonical, OwnerSeededInverseRoot.SeededNeighborhood.refine,
    InverseRootPolynomial.Model.overlapRefine] using next

/-- Every original prepared edge in the ordered list has both endpoints in the specified retained box. -/
def EndpointsIn (box : Box) : List (CenteredEdge curve differential) → Prop
  | [] => True
  | parent :: rest => box.Contains (parent.edge.point 0) ∧ box.Contains (parent.edge.point 1) ∧ EndpointsIn box rest

open Purelib.Curves.Hyperelliptic.Integration in
/-- Propagate original model alignment along a retained geometric and root-name chain of covered prepared edges.

Each original edge has both endpoints in the model box. The exact covered-parent certificates and incoming root
equivalences transport alignment to the final retained endpoint and name. -/
theorem alongChain : ∀ {parents : List (CenteredEdge curve differential)} {start finish : LiftedPoint}
    {first last : Named} {count : Nat},
    DirectPathChain parents (start := start) (finish := finish) → RootChain parents first last →
    Observation.UniformPreparedMesh.CoveredParents count parents → EndpointsIn box parents →
    RootAligned model start.coordinate first → RootAligned model finish.coordinate last
  | [], _, _, _, _, _, .nil _, .nil equivalent, .nil, _, aligned => aligned.changeName equivalent
  | _ :: _, _, _, _, _, _, .cons parent chain, .cons _ entry roots, .cons patch covered remaining, inside, aligned => by
      have initial : RootAligned model (parent.edge.point 0) (parent.edge.rootName 0 parent.edge.baseInside) := by
        rw [parent.edge.point_zero]
        exact aligned.changeName entry
      have advanced : RootAligned model (parent.edge.point 1) (parent.edge.rootName 1 (by decide)) :=
        advance patch covered inside.1 inside.2.1 initial
      rw [parent.edge.point_one] at advanced
      exact alongChain chain roots remaining inside.2.2 advanced

end Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation

end
