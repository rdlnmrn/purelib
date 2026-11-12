module

public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial
public import Purelib.Riemann.Integration.PreparedParentSplitting.Comparison
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic

/-! # Bounded primitive readback from retained polynomial models

The original occurrence index selects the cached primitive polynomial.
Its endpoint increments read the same model bank in order and sum to that
bank's exact integral sample, without executing any model factory.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents.PolynomialWork.Models

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.UniformRequest (PolynomialModel)

variable {genus count floor stage : Nat} {curve : HyperellipticCurve genus} {basis : Differential genus}
    {differential : OddPowerDifferential curve.polynomial}

/-- Read the whole cached primitive polynomial at one original bounded model occurrence. -/
@[expose] def primitivePolynomial {parents : List (CenteredEdge curve basis)}
    (covered : CoveredParents count parents) (work : PolynomialWork covered floor differential)
    (models : work.Models stage) (index : Fin parents.length) : CoefficientPolynomial :=
  let selected : Entry work stage index := entry models index
  (PolynomialModel.primitive (curve := curve) selected.2.val).primitive.value

/-- The first bounded read is the first stored model's complete primitive polynomial. -/
theorem primitivePolynomial_zero {parent : CenteredEdge curve basis}
    {parents : List (CenteredEdge curve basis)}
    (covered : CoveredParents count (parent :: parents)) (work : PolynomialWork covered floor differential)
    (models : work.Models stage) : primitivePolynomial covered work models 0 =
      (PolynomialModel.primitive (curve := curve) models.1.2.val).primitive.value := by
  cases covered
  rfl

/-- A successor index reads the same original tail model without executing its factory. -/
theorem primitivePolynomial_succ {parent : CenteredEdge curve basis}
    {parents : List (CenteredEdge curve basis)}
    {patch : Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
    {inside : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    (covered : CoveredParents count parents) (work : PolynomialWork (.cons patch inside covered) floor differential)
    (models : work.Models stage) (index : Fin parents.length) :
    primitivePolynomial (.cons patch inside covered) work models index.succ =
      primitivePolynomial covered work.2 models.2 index := by rfl

/-- Read each original model's primitive endpoint increment in its retained occurrence order. -/
@[expose] def increments : {parents : List (CenteredEdge curve basis)} →
    (covered : CoveredParents count parents) → (work : PolynomialWork covered floor differential) →
    work.Models stage → List Canonical
  | [], .nil, _, _ => []
  | parent :: _, .cons _ _ covered, work, models =>
      let primitive := PolynomialModel.primitive (curve := curve) models.1.2.val
      (primitive.primitive.value.eval (parent.edge.point 1) -
        primitive.primitive.value.eval (parent.edge.point 0)) :: increments covered work.2 models.2

/-- The ordered primitive increments sum to the same original model bank's exact integral sample. -/
theorem increments_integral : {parents : List (CenteredEdge curve basis)} →
    (covered : CoveredParents count parents) → (work : PolynomialWork covered floor differential) →
    (models : work.Models stage) →
    gaussianSum (increments covered work models) = (PathModel.mk (cells covered work models)).integralSample
  | [], .nil, _, _ => rfl
  | parent :: _, .cons _ _ covered, work, models => by
      let model := models.1.2.val
      let primitive := PolynomialModel.primitive (curve := curve) model
      have head := PolynomialModel.integralSample_eq (curve := curve) model
      have tail := increments_integral covered work.2 models.2
      have finish := congrArg primitive.primitive.value.eval parent.edge.point_one
      have start := congrArg primitive.primitive.value.eval parent.edge.point_zero
      have increment := (congrArg₂ (fun last first : Canonical => last - first) finish start).trans head.symm
      change (primitive.primitive.value.eval (parent.edge.point 1) -
        primitive.primitive.value.eval (parent.edge.point 0)) + gaussianSum (increments covered work.2 models.2) =
        (PolynomialModel.pullback (curve := curve) model).model.integralSample +
          (PathModel.mk (cells covered work.2 models.2)).integralSample
      exact (congrArg (fun value => value + gaussianSum (increments covered work.2 models.2)) increment).trans
        (congrArg (fun value => (PolynomialModel.pullback (curve := curve) model).model.integralSample + value) tail)

/-- The actual split bank reads these SAME bounded original primitive polynomials in their original parent order. -/
theorem parentSplits_increments
    {columns rows : Nat} {geometry : Riemann.Normalization.RectangularInverseModels.Geometry columns rows}
    {cuts : Riemann.Paths.RectangularSegmentSplitting.GridCuts geometry} :
    {parents : List (CenteredEdge curve basis)} → (covered : CoveredParents count parents) →
    (work : PolynomialWork covered floor differential) → (models : work.Models stage) →
    (splits : Riemann.Integration.PreparedParentSplitting.ParentSplits cuts parents) →
    splits.primitiveIncrements (fun position point => (primitivePolynomial covered work models position).eval point) =
      increments covered work models
  | [], .nil, _, _, .nil => rfl
  | parent :: _, .cons patch inside covered, work, models, .cons split tail => by
      have head := primitivePolynomial_zero (.cons patch inside covered) work models
      have sameTail := tail.primitiveIncrements_congr
        (fun position point => (primitivePolynomial (.cons patch inside covered) work models position.succ).eval point)
        (fun position point => (primitivePolynomial covered work.2 models.2 position).eval point)
        (fun position point => congrArg (fun polynomial : CoefficientPolynomial => polynomial.eval point)
          (primitivePolynomial_succ covered work models position))
      have actualTail := sameTail.trans (parentSplits_increments covered work.2 models.2 tail)
      change ((primitivePolynomial (.cons patch inside covered) work models 0).eval (parent.edge.point 1) -
          (primitivePolynomial (.cons patch inside covered) work models 0).eval (parent.edge.point 0)) :: _ = _ :: _
      exact congrArg₂ List.cons
        (congrArg (fun polynomial : CoefficientPolynomial =>
          polynomial.eval (parent.edge.point 1) - polynomial.eval (parent.edge.point 0)) head) actualTail

/-- The original split bank's unchanged primitive increments read the exact integral of the SAME actual model cells. -/
theorem parentSplits_integral
    {columns rows : Nat} {geometry : Riemann.Normalization.RectangularInverseModels.Geometry columns rows}
    {cuts : Riemann.Paths.RectangularSegmentSplitting.GridCuts geometry}
    {parents : List (CenteredEdge curve basis)} (covered : CoveredParents count parents)
    (work : PolynomialWork covered floor differential) (models : work.Models stage)
    (splits : Riemann.Integration.PreparedParentSplitting.ParentSplits cuts parents) :
    gaussianSum (splits.primitiveIncrements
      (fun position point => (primitivePolynomial covered work models position).eval point)) =
      (PathModel.mk (cells covered work models)).integralSample :=
  (congrArg gaussianSum (parentSplits_increments covered work models splits)).trans
    (increments_integral covered work models)

universe u

/-- Reindex one whole original cover/work/model bank jointly along an exact original parent-list equality.

The continuation receives the same actual caches with whole HEq readbacks
and the exact integral identity. No patch, model, polynomial or source
constructor is executed by this transport.
-/
def withParents {first last : List (CenteredEdge curve basis)} (same : first = last)
    (covered : CoveredParents count first) (work : PolynomialWork covered floor differential)
    (models : work.Models stage) {Result : Sort u}
    (consume : (viewed : CoveredParents count last) → viewed = covered.castParents same → HEq viewed covered →
      (viewedWork : PolynomialWork viewed floor differential) → HEq viewedWork work →
      (viewedModels : viewedWork.Models stage) → HEq viewedModels models →
      (PathModel.mk (cells viewed viewedWork viewedModels)).integralSample =
        (PathModel.mk (cells covered work models)).integralSample → Result) : Result := by
  cases same
  exact consume covered rfl HEq.rfl work HEq.rfl models HEq.rfl rfl

/-- Whole Work equality and model-cache HEq preserve the actual polynomial integral sample.

Equality elimination transports the complete nominal work and dependent
model cache together. It does not execute either producer or unfold the
ordered model integrals beneath a function.
-/
theorem integral_congr {parents : List (CenteredEdge curve basis)} {covered : CoveredParents count parents}
    {first last : PolynomialWork covered floor differential}
    (sameWork : first = last) (firstModels : first.Models stage) (lastModels : last.Models stage)
    (sameModels : HEq firstModels lastModels) :
    (PathModel.mk (Models.cells covered first firstModels)).integralSample =
      (PathModel.mk (Models.cells covered last lastModels)).integralSample := by
  cases sameWork
  cases sameModels
  rfl

/-- Transport a GIVEN whole work/model pair along equality of its original covered-parent cache.

Only the nominal cover index changes. The continuation receives the same
actual work and model banks with complete HEq witnesses and their literal
integral equality. No cover, inverse, primitive, polynomial or model factory
is executed to recover either input.
-/
def withCovered {parents : List (CenteredEdge curve basis)}
    {first last : CoveredParents count parents} (same : first = last)
    (work : PolynomialWork first floor differential) (models : work.Models stage) {Result : Sort u}
    (consume : (viewedWork : PolynomialWork last floor differential) → HEq viewedWork work →
      (viewedModels : viewedWork.Models stage) → HEq viewedModels models →
      (PathModel.mk (cells last viewedWork viewedModels)).integralSample =
        (PathModel.mk (cells first work models)).integralSample → Result) : Result := by
  cases same
  exact consume work HEq.rfl models HEq.rfl rfl

end Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents.PolynomialWork.Models

end
