module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Primitive
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Primitive.Subedges
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Integration.Polynomial.Gaussian.Path.Primitive
import Purelib.Data.List.Append
import Purelib.Tactic.Ring

/-! # The original primitive bank on a retained rooted child source list

The all-query rooted refinement partitions the literal child list into
ancestor blocks. Structural prefix/suffix views consume the original
cover and source product. Each ancestor polynomial telescopes within its
own block; its independent constant is never normalized against another
polynomial. Finite Cauchy charges the actual child count and movement.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic
  (gaussianSum gaussianNormSqSum gaussianSum_append gaussianNormSqSum_append)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain CenteredPathChain)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledLocalRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (coefficientMaximum localCoefficient)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
  (RootSubedge RootSubedgeBlock RootSubedgeRefinement)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis primitiveBasis : Differential 1}
    {count childCount floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

/-- Read the literal prefix of an original covering spine without another patch acquisition. -/
private def firstCover : (first last : List (CenteredEdge (Fibre.frameCurve frame) basis)) →
    CoveredParents childCount (first ++ last) → CoveredParents childCount first
  | [], _, _ => .nil
  | _ :: first, last, .cons patch inside tail => .cons patch inside (firstCover first last tail)

/-- Read the literal suffix of the same covering spine without another containment inspection. -/
private def lastCover : (first last : List (CenteredEdge (Fibre.frameCurve frame) basis)) →
    CoveredParents childCount (first ++ last) → CoveredParents childCount last
  | [], _, covered => covered
  | _ :: first, last, .cons _ _ tail => lastCover first last tail

/-- Read the same stored prefix source caches at their original covering indices. -/
private def firstSources : (first last : List (CenteredEdge (Fibre.frameCurve frame) basis)) →
    (covered : CoveredParents childCount (first ++ last)) → PreparedParents covered floor targets →
      PreparedParents (firstCover first last covered) floor targets
  | [], _, _, _ => PUnit.unit
  | _ :: first, last, .cons _ _ covered, prepared =>
      ⟨prepared.1, firstSources first last covered prepared.2⟩

/-- Read the same stored suffix source caches without executing their preparation rule. -/
private def lastSources : (first last : List (CenteredEdge (Fibre.frameCurve frame) basis)) →
    (covered : CoveredParents childCount (first ++ last)) → PreparedParents covered floor targets →
      PreparedParents (lastCover first last covered) floor targets
  | [], _, _, prepared => prepared
  | _ :: first, last, .cons _ _ covered, prepared => lastSources first last covered prepared.2

/-- Read the actual selected-channel model samples in their unchanged occurrence order. -/
private def sourceValues (channel : Fin 6) : {children : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents childCount children) → PreparedParents covered floor targets → List Canonical
  | [], .nil, _ => []
  | _ :: _, .cons _ _ covered, prepared =>
      (prepared.1.preparation.cell.models.cell channel).integralSample :: sourceValues channel covered prepared.2

/-- Splitting the stored source product only splits its literal sample list. -/
private theorem sourceValues_split (channel : Fin 6) :
    (first last : List (CenteredEdge (Fibre.frameCurve frame) basis)) →
    (covered : CoveredParents childCount (first ++ last)) → (prepared : PreparedParents covered floor targets) →
    sourceValues channel covered prepared =
      sourceValues channel (firstCover first last covered) (firstSources first last covered prepared) ++
        sourceValues channel (lastCover first last covered) (lastSources first last covered prepared)
  | [], _, _, _ => rfl
  | _ :: first, last, .cons _ _ covered, prepared =>
      congrArg (List.cons (prepared.1.preparation.cell.models.cell channel).integralSample)
        (sourceValues_split channel first last covered prepared.2)

/-- The retained sample list is exactly the original source path's selected-channel integral sample. -/
private theorem sourceValues_sum (channel : Fin 6) : {children : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents childCount children) → (prepared : PreparedParents covered floor targets) →
    {start finish : LiftedPoint 2} → (chain : CenteredPathChain children (start := start) (finish := finish)) →
    gaussianSum (sourceValues channel covered prepared) =
      (PathModel.mk ((sources covered prepared chain).cells channel)).integralSample
  | [], .nil, .unit, _, _, .nil point =>
      (congrArg (fun cells => (PathModel.mk cells).integralSample)
        (Path.cells_nil (parameter := parameter) point channel)).symm
  | _ :: _, .cons _ _ covered, prepared, _, _, .cons _ chain => by
      have cells := congrArg (fun cells => (PathModel.mk cells).integralSample)
        (Path.cells_cons prepared.1.preparation.cell (sources covered prepared.2 chain) channel)
      change (prepared.1.preparation.cell.models.cell channel).integralSample +
        gaussianSum (sourceValues channel covered prepared.2) = _
      exact (congrArg ((prepared.1.preparation.cell.models.cell channel).integralSample + ·)
        (sourceValues_sum channel covered prepared.2 chain)).trans cells.symm

/-- The retained displacement-cost sum splits at the exact original child block. -/
private theorem displacementCost_split (first last : List (CenteredEdge (Fibre.frameCurve frame) basis)) :
    displacementCost (first ++ last) = displacementCost first + displacementCost last := by
  induction first with
  | nil => change displacementCost last = 0 + displacementCost last; ring1
  | cons child first ih =>
      rewrite [List.cons_append, displacementCost_cons, displacementCost_cons, ih]
      ring1

/-- Read one polynomial's endpoint error against each original stored child model. -/
private def polynomialErrors (primitive : Canonical → Canonical) (channel : Fin 6) :
    {children : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents childCount children) → PreparedParents covered floor targets → List Canonical
  | [], .nil, _ => []
  | child :: _, .cons _ _ covered, prepared =>
      (primitive (child.edge.point 1) - primitive (child.edge.point 0) -
        (prepared.1.preparation.cell.models.cell channel).integralSample) ::
      polynomialErrors primitive channel covered prepared.2

/-- The polynomial error list retains every original child occurrence. -/
private theorem polynomialErrors_length (primitive : Canonical → Canonical) (channel : Fin 6) :
    {children : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents childCount children) → (prepared : PreparedParents covered floor targets) →
    (polynomialErrors primitive channel covered prepared).length = children.length
  | [], .nil, _ => rfl
  | _ :: _, .cons _ _ covered, prepared =>
      congrArg Nat.succ (polynomialErrors_length primitive channel covered prepared.2)

/-- One polynomial's ordered error sum retains the original child increments and source samples. -/
private theorem polynomialErrors_sum (primitive : Canonical → Canonical) (channel : Fin 6) :
    {children : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents childCount children) → (prepared : PreparedParents covered floor targets) →
    gaussianSum (polynomialErrors primitive channel covered prepared) =
      Primitive.incrementSum primitive (children.map CenteredEdge.model) -
        gaussianSum (sourceValues channel covered prepared)
  | [], .nil, _ => by change (0 : Canonical) = 0 - 0; ring1
  | child :: _, .cons _ _ covered, prepared => by
      change (primitive (child.edge.point 1) - primitive (child.edge.point 0) -
        (prepared.1.preparation.cell.models.cell channel).integralSample) +
          gaussianSum (polynomialErrors primitive channel covered prepared.2) = _
      rewrite [polynomialErrors_sum primitive channel covered prepared.2]
      change _ = (primitive (child.edge.point 1) - primitive (child.edge.point 0) +
        Primitive.incrementSum primitive _) -
        ((prepared.1.preparation.cell.models.cell channel).integralSample + gaussianSum _)
      ring1

/-- Read each original occurrence's own primitive increment without identifying equal parent values. -/
@[expose] def primitiveIncrements : (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) →
    (Fin parents.length → Canonical → Canonical) → List Canonical
  | [], _ => []
  | parent :: parents, primitive =>
      (primitive 0 (parent.edge.point 1) - primitive 0 (parent.edge.point 0)) ::
        primitiveIncrements parents (fun index => primitive index.succ)

/-- Derived local errors add on the same retained child block and source channel. -/
private theorem polynomialErrors_normSum_le
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} (primitive : Canonical → Canonical)
    (channel : Fin 6) (charge : Rational)
    (localBound : ∀ {child : CenteredEdge (Fibre.frameCurve frame) basis}, RootSubedge parent child →
      (patch : PreparedPatch child) → (inside : (patch.neighborhood childCount).box.Contains (child.edge.point 1)) →
      (prepared : PreparedParent patch childCount floor inside targets) →
      Norm.Basic.normSq (primitive (child.edge.point 1) - primitive (child.edge.point 0) -
        (prepared.preparation.cell.models.cell channel).integralSample) ≤ charge * PreparedParent.cost child) :
    {children : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (roots : RootSubedgeBlock parent children) → (covered : CoveredParents childCount children) →
    (prepared : PreparedParents covered floor targets) →
    gaussianNormSqSum (polynomialErrors primitive channel covered prepared) ≤ charge * displacementCost children
  | [], .nil, .nil, _ => by
      change (0 : Rational) ≤ charge * 0
      rewrite [Data.Rat.Fraction.Field.mul_zero_direct]
      exact Data.Rat.Fraction.Order.Basic.le_refl 0
  | _ :: _, .cons relation roots, .cons patch inside covered, prepared => by
      have head := localBound relation patch inside prepared.1
      have tail := polynomialErrors_normSum_le primitive channel charge localBound roots covered prepared.2
      change Canonical.normSq _ + gaussianNormSqSum _ ≤ _
      rewrite [← Norm.Basic.normSq_eq_canonical]
      exact (Arithmetic.add_le_add_direct head tail).trans_eq (by
        rewrite [displacementCost_cons]
        ring1)

/-- Read each retained ancestor occurrence's own polynomial errors on its exact rooted child block. -/
private def refinementErrors
    {parents children : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (primitive : Fin parents.length → Canonical → Canonical) (channel : Fin 6)
    (refinement : RootSubedgeRefinement parents children) (covered : CoveredParents childCount children)
    (prepared : PreparedParents covered floor targets) : List Canonical :=
  RootSubedgeRefinement.casesOn
    (motive := fun parents children _ => (Fin parents.length → Canonical → Canonical) →
      (covered : CoveredParents childCount children) → PreparedParents covered floor targets → List Canonical)
    refinement
    (fun _primitive _covered _prepared => [])
    (fun {_parent _parents block children} _chain _roots refinement primitive covered prepared =>
      polynomialErrors (primitive 0) channel
        (firstCover block children covered) (firstSources block children covered prepared) ++
      refinementErrors (fun index => primitive index.succ) channel refinement
        (lastCover block children covered) (lastSources block children covered prepared))
    primitive covered prepared
termination_by structural refinement

/-- The complete error list retains one entry for every literal child occurrence. -/
private theorem refinementErrors_length
    {parents children : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (primitive : Fin parents.length → Canonical → Canonical) (channel : Fin 6)
    (refinement : RootSubedgeRefinement parents children) (covered : CoveredParents childCount children)
    (prepared : PreparedParents covered floor targets) :
    (refinementErrors primitive channel refinement covered prepared).length = children.length :=
  RootSubedgeRefinement.casesOn
    (motive := fun parents children refinement =>
      (primitive : Fin parents.length → Canonical → Canonical) →
      (covered : CoveredParents childCount children) → (prepared : PreparedParents covered floor targets) →
      (refinementErrors primitive channel refinement covered prepared).length = children.length)
    refinement
    (fun _primitive covered _prepared => by cases covered; rfl)
    (fun {_parent _parents block children} _chain _roots refinement primitive covered prepared => by
      change (polynomialErrors (primitive 0) channel
        (firstCover block children covered) (firstSources block children covered prepared) ++
        refinementErrors (fun index => primitive index.succ) channel refinement
          (lastCover block children covered) (lastSources block children covered prepared)).length = _
      rewrite [List.length_append, polynomialErrors_length,
        refinementErrors_length (fun index => primitive index.succ) channel refinement
          (lastCover block children covered) (lastSources block children covered prepared), List.length_append]
      rfl)
    primitive covered prepared
termination_by structural refinement

/-- Original child chains telescope only their own retained ancestor primitive, including empty blocks. -/
private theorem refinementErrors_sum
    {parents children : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (primitive : Fin parents.length → Canonical → Canonical) (channel : Fin 6)
    (refinement : RootSubedgeRefinement parents children) (covered : CoveredParents childCount children)
    (prepared : PreparedParents covered floor targets) :
    gaussianSum (refinementErrors primitive channel refinement covered prepared) =
      gaussianSum (primitiveIncrements parents primitive) - gaussianSum (sourceValues channel covered prepared) :=
  RootSubedgeRefinement.casesOn
    (motive := fun parents children refinement =>
      (primitive : Fin parents.length → Canonical → Canonical) →
      (covered : CoveredParents childCount children) → (prepared : PreparedParents covered floor targets) →
      gaussianSum (refinementErrors primitive channel refinement covered prepared) =
        gaussianSum (primitiveIncrements parents primitive) - gaussianSum (sourceValues channel covered prepared))
    refinement
    (fun _primitive covered _prepared => by
      cases covered
      change (0 : Canonical) = 0 - 0
      ring1)
    (fun {parent _parents block children} chain _roots refinement primitive covered prepared => by
      have head := Riemann.Paths.PreparedPrimitivePaths.incrementSum_eq (primitive 0) chain
      have tail := refinementErrors_sum (fun index => primitive index.succ) channel refinement
        (lastCover block children covered) (lastSources block children covered prepared)
      change gaussianSum (polynomialErrors (primitive 0) channel
        (firstCover block children covered) (firstSources block children covered prepared) ++
        refinementErrors (fun index => primitive index.succ) channel refinement
          (lastCover block children covered) (lastSources block children covered prepared)) = _
      rewrite [gaussianSum_append, polynomialErrors_sum, head, tail,
        sourceValues_split channel block children covered prepared, gaussianSum_append]
      change _ = (primitive 0 (parent.edge.point 1) - primitive 0 (parent.edge.point 0)) +
        gaussianSum (primitiveIncrements _ (fun index => primitive index.succ)) - _
      rewrite [parent.edge.point_one, parent.edge.point_zero]
      ring1)
    primitive covered prepared
termination_by structural refinement

/-- Derived per-occurrence local bounds sum on the same literal rooted refinement. -/
private theorem refinementErrors_normSum_le
    {parents children : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (primitive : Fin parents.length → Canonical → Canonical) (channel : Fin 6) (charge : Rational)
    (refinement : RootSubedgeRefinement parents children) (covered : CoveredParents childCount children)
    (prepared : PreparedParents covered floor targets)
    (localBound : ∀ (index : Fin parents.length) {child : CenteredEdge (Fibre.frameCurve frame) basis},
      RootSubedge (parents[index.val]'index.isLt) child →
      (patch : PreparedPatch child) → (inside : (patch.neighborhood childCount).box.Contains (child.edge.point 1)) →
      (prepared : PreparedParent patch childCount floor inside targets) →
      Norm.Basic.normSq (primitive index (child.edge.point 1) - primitive index (child.edge.point 0) -
        (prepared.preparation.cell.models.cell channel).integralSample) ≤ charge * PreparedParent.cost child) :
    gaussianNormSqSum (refinementErrors primitive channel refinement covered prepared) ≤
      charge * displacementCost children :=
  RootSubedgeRefinement.casesOn
    (motive := fun parents children refinement =>
      (primitive : Fin parents.length → Canonical → Canonical) →
      (covered : CoveredParents childCount children) → (prepared : PreparedParents covered floor targets) →
      (∀ (index : Fin parents.length) {child : CenteredEdge (Fibre.frameCurve frame) basis},
        RootSubedge (parents[index.val]'index.isLt) child →
        (patch : PreparedPatch child) → (inside : (patch.neighborhood childCount).box.Contains (child.edge.point 1)) →
        (prepared : PreparedParent patch childCount floor inside targets) →
        Norm.Basic.normSq (primitive index (child.edge.point 1) - primitive index (child.edge.point 0) -
          (prepared.preparation.cell.models.cell channel).integralSample) ≤ charge * PreparedParent.cost child) →
      gaussianNormSqSum (refinementErrors primitive channel refinement covered prepared) ≤
        charge * displacementCost children)
    refinement
    (fun _primitive covered _prepared _localBound => by
      cases covered
      change (0 : Rational) ≤ charge * 0
      rewrite [Data.Rat.Fraction.Field.mul_zero_direct]
      exact Data.Rat.Fraction.Order.Basic.le_refl 0)
    (fun {_parent _parents block children} _chain roots refinement primitive covered prepared localBound => by
      have head := polynomialErrors_normSum_le (primitive 0) channel charge (localBound 0) roots
        (firstCover block children covered) (firstSources block children covered prepared)
      have tail := refinementErrors_normSum_le (fun index => primitive index.succ) channel charge refinement
        (lastCover block children covered) (lastSources block children covered prepared)
        (fun index => localBound index.succ)
      change gaussianNormSqSum (polynomialErrors (primitive 0) channel
        (firstCover block children covered) (firstSources block children covered prepared) ++
        refinementErrors (fun index => primitive index.succ) channel refinement
          (lastCover block children covered) (lastSources block children covered prepared)) ≤ _
      rewrite [gaussianNormSqSum_append]
      exact (Arithmetic.add_le_add_direct head tail).trans_eq (by
        rewrite [displacementCost_split]
        ring1))
    primitive covered prepared localBound
termination_by structural refinement

/-- Derived local primitive errors give an ordered actual-source bound on the retained rooted refinement.

The primitive lookup is indexed by original bounded occurrences, so equal
parent values may retain different caches. It is a projection view of given
polynomials, not a primitive or model factory. The concrete local estimates
supply the error bounds internally; the unchanged block chains supply exact
endpoint cancellation. No charge nonnegativity premise is needed.
-/
theorem rooted_increment_error_le {parents children : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (primitive : Fin parents.length → Canonical → Canonical) (channel : Fin 6) (charge : Rational)
    (refinement : RootSubedgeRefinement parents children)
    (covered : CoveredParents childCount children) (prepared : PreparedParents covered floor targets)
    (localBound : ∀ (index : Fin parents.length) {child : CenteredEdge (Fibre.frameCurve frame) basis},
      RootSubedge (parents[index.val]'index.isLt) child →
      (patch : PreparedPatch child) → (inside : (patch.neighborhood childCount).box.Contains (child.edge.point 1)) →
      (prepared : PreparedParent patch childCount floor inside targets) →
      Norm.Basic.normSq (primitive index (child.edge.point 1) - primitive index (child.edge.point 0) -
        (prepared.preparation.cell.models.cell channel).integralSample) ≤ charge * PreparedParent.cost child)
    {start finish : LiftedPoint 2} (chain : CenteredPathChain children (start := start) (finish := finish)) :
    Norm.Basic.normSq (gaussianSum (primitiveIncrements parents primitive) -
      (PathModel.mk ((sources covered prepared chain).cells channel)).integralSample) ≤
        charge * movementMass children := by
  have cauchy := Norm.Sum.Basic.normSq_gaussianSum_le (refinementErrors primitive channel refinement covered prepared)
  rewrite [← Norm.Basic.normSq_eq_canonical, refinementErrors_sum primitive channel refinement covered prepared,
    sourceValues_sum channel covered prepared chain,
    refinementErrors_length primitive channel refinement covered prepared] at cauchy
  have total := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (refinementErrors_normSum_le primitive channel charge refinement covered prepared localBound)
    (Data.Rat.Fraction.Cast.Order.natCast_le_direct (m := 0) (n := children.length) (Nat.zero_le children.length))
  exact (cauchy.trans total).trans_eq (by
    rewrite [← countCost_eq_movementMass]
    ring1)

/-- Project the already retained request primitive at each original bounded occurrence. -/
private def requestPrimitives {target : Rational} :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    RequestedParents count target (parents.map (recastCenteredEdge primitiveBasis)) →
      Fin parents.length → Canonical → Canonical
  | [], .nil, index => Fin.elim0 index
  | _ :: _, .cons request requests, index =>
      Fin.cases request.request.model.primitive.value.eval (requestPrimitives requests) index

/-- Projected request increments are the original literal cached increment list. -/
private theorem requestPrimitives_increments {target : Rational} :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (requests : RequestedParents count target (parents.map (recastCenteredEdge primitiveBasis))) →
    primitiveIncrements parents (requestPrimitives requests) = requests.increments
  | [], .nil => rfl
  | parent :: _, .cons request requests =>
      congrArg (List.cons (request.request.model.primitive.value.eval (parent.edge.point 1) -
        request.request.model.primitive.value.eval (parent.edge.point 0))) (requestPrimitives_increments requests)

/-- The original retained coefficient maximum derives each occurrence-indexed local estimate. -/
private theorem requestPrimitives_local {target coefficientTarget : Rational}
    (zero : primitiveBasis.exponent = 0) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (requests : RequestedParents count target (parents.map (recastCenteredEdge primitiveBasis))) →
    coefficientMaximum requests < coefficientTarget → (index : Fin parents.length) →
    {child : CenteredEdge (Fibre.frameCurve frame) basis} → RootSubedge (parents[index.val]'index.isLt) child →
    (patch : PreparedPatch child) → (inside : (patch.neighborhood childCount).box.Contains (child.edge.point 1)) →
    (prepared : PreparedParent patch childCount floor inside targets) →
    Norm.Basic.normSq (requestPrimitives requests index (child.edge.point 1) -
      requestPrimitives requests index (child.edge.point 0) -
        prepared.preparation.cell.models.valueZero.model.integralSample) ≤
      16 * (targets.localBound + coefficientTarget) * PreparedParent.cost child
  | [], .nil, _paid, index => Fin.elim0 index
  | parent :: _, .cons request requests, paid, index => by
      refine Fin.cases ?_ ?_ index
      · intro relation patch inside prepared
        have headPaid : localCoefficient request < coefficientTarget :=
          (Data.Rat.Fraction.Order.Basic.le_max_left _ _).trans_lt paid
        let controlled : ControlledLocalRequest (recastCenteredEdge primitiveBasis parent) count
            target coefficientTarget 0 := ⟨request, headPaid, Nat.zero_le request.request.index⟩
        exact PreparedParent.subedge_primitive_paid_le controlled zero relation prepared
      · intro index
        exact requestPrimitives_local zero requests
          ((Data.Rat.Fraction.Order.Basic.le_max_right _ _).trans_lt paid) index

/-- The actual child value-zero model is compared with the same ordered ancestor primitive increments.

No equality between independently prepared parent and child sources is
required. The retained all-query rooted refinement supplies each signed
coefficient comparison. Each block's original chain supplies its literal
endpoint cancellation; finite Cauchy retains the entire child count,
including repeated and stationary occurrences.
-/
theorem rooted_primitive_error_le {parents children : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {target coefficientTarget : Rational}
    (requests : RequestedParents count target (parents.map (recastCenteredEdge primitiveBasis)))
    (zero : primitiveBasis.exponent = 0) (refinement : RootSubedgeRefinement parents children)
    (covered : CoveredParents childCount children) (prepared : PreparedParents covered floor targets)
    (paid : coefficientMaximum requests < coefficientTarget) {start finish : LiftedPoint 2}
    (chain : CenteredPathChain children (start := start) (finish := finish)) :
    Norm.Basic.normSq (gaussianSum requests.increments -
      (PathModel.mk ((sources covered prepared chain).cells 0)).integralSample) ≤
        16 * (targets.localBound + coefficientTarget) * movementMass children := by
  have original := rooted_increment_error_le (requestPrimitives requests) 0
    (16 * (targets.localBound + coefficientTarget)) refinement covered prepared
    (requestPrimitives_local zero requests paid) chain
  rewrite [requestPrimitives_increments requests] at original
  exact original

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
