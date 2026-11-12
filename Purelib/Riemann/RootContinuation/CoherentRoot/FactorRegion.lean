module

public import Purelib.Riemann.RootContinuation.CoherentRoot.PairSeparation
public import Purelib.RootIsolation.State.WindingOne.Coprime
public import Purelib.Polynomial.Clearance.Box.Region.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Operations
public import Purelib.Polynomial.Winding.Box.Product
import Purelib.Riemann.RootContinuation.CoherentRoot.Refinement
import Purelib.Polynomial.Winding.Box.Region
public import Purelib.RootIsolation.Exact.Extraction
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Nat.Order
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Polynomial.Dense.Gaussian.Roots.Linear.Evaluation
public import Purelib.Geometry.Rational.Box.Outside
public import Purelib.Geometry.Rational.Box.Hull
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Polynomial.Clearance.Box.Boundary.Constant
public import Purelib.Polynomial.Clearance.Box.Boundary.Translated
import Purelib.Polynomial.Winding.Box.Constant
import Purelib.Polynomial.Winding.Box.Affine.Outside
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Basic

/-!
# Original-source winding regions at cached factor-root stages

The checked source factorization and retained cofactor determine one positive
request. An actual local constant or affine presentation can supply its own
clearance and zero winding; the absent request keeps global coprime protection.
Every region consumes the same original root cache and source identity.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Polynomial.Dense.Gaussian.Factorization
open Purelib.Polynomial.Dense.Gaussian.Coprime.Basic (CoprimeCertificate)
open Purelib.Data.Rat.Fraction
open Purelib.RootIsolation
open Purelib.Polynomial
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational
open Purelib.Geometry.Rational
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Clearance.Box.Line.Basic (VerticalLineClearance HorizontalLineClearance)
open Purelib.Polynomial.Clearance.Box

namespace FactorRegion

/-- An original nonzero constant or affine cofactor with its exact root excluded from the original box.

This reducible view retains the original normalized coefficient identity or
complete original affine root data. The outside-side witness concerns that
same cached affine point and the original factor-root owner box.
-/
abbrev LocalCofactor (cofactor : GaussianPolynomial) (box : Box) :=
  Sum {constant : Gaussian //
      cofactor.normalize = Dense.Gaussian.Constants.gaussianConstant constant ∧ constant ≠ 0}
    ((data : Dense.Gaussian.Roots.Linear.RootData cofactor) × Box.OutsideSide box data.point)

namespace LocalCofactor

/-- Retain the same exact cofactor presentation at a proved original subbox.

Constant data are unchanged. Affine data keep the complete original root
record and transport only its actual outside-side certificate through the
supplied refinement; no coefficient or root computation is repeated.
-/
def ofRefines {cofactor : GaussianPolynomial} {inner outer : Box}
    (requested : LocalCofactor cofactor outer) (refines : inner.Refines outer) :
    LocalCofactor cofactor inner :=
  match requested with
  | .inl constant => .inl constant
  | .inr affine => .inr ⟨affine.1, affine.2.ofRefines refines⟩

/-- Check one exact constant or affine cofactor presentation against the supplied original box.

The retained coefficient polynomial determines its degree and its original
normalized constant or affine root data. An affine presentation is returned
only after the same computed root is checked outside the actual supplied box.
Unresolved degree or exclusion checks return no local presentation.
-/
@[expose] def inspect (cofactor : GaussianPolynomial) (nonzero : cofactor.isZero = false) (box : Box) :
    Option (LocalCofactor cofactor box) :=
  if constant : cofactor.natDegree = 0 then
    some (.inl ⟨cofactor.leadingCoeff,
      DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero nonzero constant,
      DensePolynomial.leadingCoeff_ne_zero nonzero⟩)
  else if affine : cofactor.natDegree = 1 then
    let data := Dense.Gaussian.Roots.Linear.rootData affine
    if outside : ¬ box.Contains data.point then
      some (.inr ⟨data, Box.outsideSide outside⟩)
    else none
  else none

/-- The retained local cofactor lower bound uses the original coefficient and excluded-side caches. -/
@[expose] def bound {cofactor : GaussianPolynomial} {outer : Box} : LocalCofactor cofactor outer → Coordinate
  | .inl constant => Canonical.normSq constant.val
  | .inr affine => Canonical.normSq affine.1.leading * affine.2.margin

/-- Produce clearance on an actual retained subbox using the same original local cofactor presentation.

The bound keeps the original outside-side margin even for later subboxes.
The coefficient identity transports original constant evaluations; affine
clearance consumes the same retained leading coefficient and exact root.
-/
@[expose] def clearance {cofactor : GaussianPolynomial} {outer box : Box}
    (requested : LocalCofactor cofactor outer) (refines : box.Refines outer) :
    Boundary.Basic.BoundaryClearance cofactor box :=
  match requested with
  | .inl constant =>
      let retained := Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance
        constant.property.2 box
      { bound := retained.bound
        positive := retained.positive
        lower := by
          intro point boundary
          have same : cofactor.eval point = (Dense.Gaussian.Constants.gaussianConstant constant.val).eval point :=
            (DensePolynomial.eval_normalize cofactor point).symm.trans
              (congrArg (fun polynomial : GaussianPolynomial => polynomial.eval point) constant.property.1)
          exact Eq.mp (congrArg (fun value : Gaussian => retained.bound ≤ Canonical.normSq value) same.symm)
            (retained.lower point boundary) }
  | .inr affine => Clearance.Box.Boundary.Translated.Affine.linear_boundaryClearance_of_outside
      affine.1 affine.2 refines

/-- Each actual local cofactor clearance retains exactly the displayed original local bound. -/
theorem clearance_bound {cofactor : GaussianPolynomial} {outer box : Box}
    (requested : LocalCofactor cofactor outer) (refines : box.Refines outer) :
    (requested.clearance refines).bound = requested.bound := by
  cases requested with
  | inl constant => rfl
  | inr affine =>
      exact Clearance.Box.Boundary.Translated.Affine.linear_boundaryClearance_of_outside_bound
        affine.1 affine.2 refines

/-- The same original local cofactor has zero winding on every proper retained subbox. -/
theorem winding_zero {cofactor : GaussianPolynomial} {outer box : Box}
    (requested : LocalCofactor cofactor outer) (refines : box.Refines outer) (proper : box.Proper) :
    Winding.Box.Basic.quadrupledBoxWinding cofactor box = 0 := by
  cases requested with
  | inl constant =>
      have normalized := (Winding.Box.Basic.quadrupledBoxWinding_normalize cofactor box).symm
      rewrite [constant.property.1] at normalized
      exact normalized.trans (Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant constant.property.2 box)
  | inr affine =>
      exact Winding.Box.Affine.Outside.quadrupledBoxWinding_linear_of_outside affine.1 proper
        (affine.2.ofRefines refines)

end LocalCofactor

/-- Enclose two original root-state boxes using their retained ambient line certificates.

Each hull side is an actual side of one input box. A source side consumes
that same original source line cache. A factor side consumes its original
factor line cache and the same locally certified cofactor on the hull,
then transports their original product through the coefficient identity.
The supplied endpoint checks ensure every retained ambient line covers the
whole hull; no axis isolation or new line search is performed.
-/
@[expose] def enclosingRegion {source factor cofactor : GaussianPolynomial} {sourceAmbient factorAmbient : Box}
    (sourceInitial : WindingOneState source sourceAmbient) (factorInitial : WindingOneState factor factorAmbient)
    (factorization : Identity.ProductIdentity source factor cofactor)
    (requested : LocalCofactor cofactor (Box.Hull.hull factorInitial.box sourceInitial.box))
    (withinSource : (Box.Hull.hull factorInitial.box sourceInitial.box).Refines sourceAmbient)
    (withinFactor : (Box.Hull.hull factorInitial.box sourceInitial.box).Refines factorAmbient) :
    Clearance.Box.Region.ClearRegion source sourceAmbient := by
  let box := Box.Hull.hull factorInitial.box sourceInitial.box
  let retained := requested.clearance (Box.refines_refl box)
  let left : VerticalLineClearance source box box.xLower :=
    if selected : factorInitial.box.xLower ≤ sourceInitial.box.xLower then
      let original := factorInitial.ambientLeftClearance.restrict withinFactor
      have coordinate : box.xLower = factorInitial.box.xLower := Fraction.Order.Basic.min_eq_left selected
      let atHull := Eq.mp (congrArg
        (fun x => VerticalLineClearance factor box x) coordinate.symm) original
      VerticalLineClearance.ofProductIdentity factorization
        atHull (Boundary.Lines.leftOfBoundary retained)
    else
      let original := sourceInitial.ambientLeftClearance.restrict withinSource
      have coordinate : box.xLower = sourceInitial.box.xLower :=
        Fraction.Order.Basic.min_eq_right ((Fraction.Order.Basic.le_total _ _).resolve_left selected)
      Eq.mp (congrArg (fun x => VerticalLineClearance source box x) coordinate.symm) original
  let right : VerticalLineClearance source box box.xUpper :=
    if selected : sourceInitial.box.xUpper ≤ factorInitial.box.xUpper then
      let original := factorInitial.ambientRightClearance.restrict withinFactor
      have coordinate : box.xUpper = factorInitial.box.xUpper := Fraction.Order.Basic.max_eq_left selected
      let atHull := Eq.mp (congrArg
        (fun x => VerticalLineClearance factor box x) coordinate.symm) original
      VerticalLineClearance.ofProductIdentity factorization
        atHull (Boundary.Lines.rightOfBoundary retained)
    else
      let original := sourceInitial.ambientRightClearance.restrict withinSource
      have coordinate : box.xUpper = sourceInitial.box.xUpper :=
        Fraction.Order.Basic.max_eq_right ((Fraction.Order.Basic.le_total _ _).resolve_left selected)
      Eq.mp (congrArg (fun x => VerticalLineClearance source box x) coordinate.symm) original
  let bottom : HorizontalLineClearance source box box.yLower :=
    if selected : factorInitial.box.yLower ≤ sourceInitial.box.yLower then
      let original := factorInitial.ambientBottomClearance.restrict withinFactor
      have coordinate : box.yLower = factorInitial.box.yLower := Fraction.Order.Basic.min_eq_left selected
      let atHull := Eq.mp (congrArg
        (fun y => HorizontalLineClearance factor box y) coordinate.symm) original
      HorizontalLineClearance.ofProductIdentity factorization
        atHull (Boundary.Lines.bottomOfBoundary retained)
    else
      let original := sourceInitial.ambientBottomClearance.restrict withinSource
      have coordinate : box.yLower = sourceInitial.box.yLower :=
        Fraction.Order.Basic.min_eq_right ((Fraction.Order.Basic.le_total _ _).resolve_left selected)
      Eq.mp (congrArg (fun y => HorizontalLineClearance source box y) coordinate.symm) original
  let top : HorizontalLineClearance source box box.yUpper :=
    if selected : sourceInitial.box.yUpper ≤ factorInitial.box.yUpper then
      let original := factorInitial.ambientTopClearance.restrict withinFactor
      have coordinate : box.yUpper = factorInitial.box.yUpper := Fraction.Order.Basic.max_eq_left selected
      let atHull := Eq.mp (congrArg
        (fun y => HorizontalLineClearance factor box y) coordinate.symm) original
      HorizontalLineClearance.ofProductIdentity factorization
        atHull (Boundary.Lines.topOfBoundary retained)
    else
      let original := sourceInitial.ambientTopClearance.restrict withinSource
      have coordinate : box.yUpper = sourceInitial.box.yUpper :=
        Fraction.Order.Basic.max_eq_right ((Fraction.Order.Basic.le_total _ _).resolve_left selected)
      Eq.mp (congrArg (fun y => HorizontalLineClearance source box y) coordinate.symm) original
  exact
    { box := box
      refinesAmbient := withinSource
      proper := Box.Hull.proper factorInitial.proper
      clearance := Boundary.Lines.boundaryOfLines left right bottom top }

/-- The enclosing region retains exactly the hull of its two original state boxes. -/
theorem enclosingRegion_box {source factor cofactor : GaussianPolynomial} {sourceAmbient factorAmbient : Box}
    (sourceInitial : WindingOneState source sourceAmbient) (factorInitial : WindingOneState factor factorAmbient)
    (factorization : Identity.ProductIdentity source factor cofactor)
    (requested : LocalCofactor cofactor (Box.Hull.hull factorInitial.box sourceInitial.box))
    (withinSource : (Box.Hull.hull factorInitial.box sourceInitial.box).Refines sourceAmbient)
    (withinFactor : (Box.Hull.hull factorInitial.box sourceInitial.box).Refines factorAmbient) :
    (enclosingRegion sourceInitial factorInitial factorization requested withinSource withinFactor).box =
      Box.Hull.hull factorInitial.box sourceInitial.box := by
  unfold enclosingRegion
  rfl

/-- Select global protection or an already-paid original starting radius for an actual local cofactor.

The absent local request retains the entire original coprime scalar operation.
An actual local presentation needs no global small-residual protection, so
its original starting radius plus one pays the same requested floor.
-/
@[expose] def target {factor cofactor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} (root : CertifiedName track)
    (coprime : CoprimeCertificate factor cofactor) (start : Nat)
    (requested : Option (LocalCofactor cofactor track.initial.box)) : Coordinate :=
  match requested with
  | none => Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius coprime ambient ^ 2
  | some _ => root.approximation.radiusSq start + 1

/-- Both actual protection request modes retain a positive squared-diagonal target. -/
theorem target_pos {factor cofactor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} (root : CertifiedName track)
    (coprime : CoprimeCertificate factor cofactor) (start : Nat)
    (requested : Option (LocalCofactor cofactor track.initial.box)) : 0 < target root coprime start requested := by
  cases requested with
  | none =>
      exact Fraction.Order.Arithmetic.pow_pos_direct
        (Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius_pos coprime ambient) 2
  | some retained =>
      exact Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
        (root.approximation.radiusSq_nonneg start) (by decide)

/-- Select the original global cofactor margin or the actual retained local coefficient/side bound. -/
@[expose] def cofactorBound {factor cofactor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient}
    (coprime : CoprimeCertificate factor cofactor)
    (requested : Option (LocalCofactor cofactor track.initial.box)) : Coordinate :=
  match requested with
  | none => Dense.Gaussian.Coprime.Bounds.Box.rightMargin coprime ambient
  | some retained => retained.bound

/-- Consume the actual global protection proof or original local cofactor cache at the same retained state. -/
@[expose] def clearanceAt {factor cofactor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} (root : CertifiedName track)
    (coprime : CoprimeCertificate factor cofactor) (start : Nat)
    (requested : Option (LocalCofactor cofactor track.initial.box))
    (current : WindingOneState factor ambient) (refines : current.box.Refines track.initial.box)
    (diagonal : current.box.diagonalSq < target root coprime start requested) :
    Boundary.Basic.BoundaryClearance cofactor current.box := by
  cases requested with
  | none => exact State.WindingOne.Coprime.rightClearance root.degreePositive coprime current diagonal.le
  | some retained => exact retained.clearance refines

/-- Both actual cofactor-clearance modes retain their same original request-specific bound. -/
theorem clearanceAt_bound {factor cofactor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} (root : CertifiedName track)
    (coprime : CoprimeCertificate factor cofactor) (start : Nat)
    (requested : Option (LocalCofactor cofactor track.initial.box))
    (current : WindingOneState factor ambient) (refines : current.box.Refines track.initial.box)
    (diagonal : current.box.diagonalSq < target root coprime start requested) :
    (clearanceAt root coprime start requested current refines diagonal).bound =
      cofactorBound (track := track) coprime requested := by
  cases requested with
  | none => rfl
  | some retained => exact retained.clearance_bound refines

/-- The same retained request proves zero cofactor winding at its actual original state. -/
theorem windingAt {factor cofactor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} (root : CertifiedName track)
    (nonzero : cofactor.isZero = false)
    (coprime : CoprimeCertificate factor cofactor) (start : Nat)
    (requested : Option (LocalCofactor cofactor track.initial.box))
    (current : WindingOneState factor ambient) (refines : current.box.Refines track.initial.box)
    (diagonal : current.box.diagonalSq < target root coprime start requested) :
    Winding.Box.Basic.quadrupledBoxWinding cofactor current.box = 0 := by
  cases requested with
  | none =>
      exact State.WindingOne.Coprime.right_winding_zero_of_nonzero root.degreePositive
        nonzero coprime current diagonal.le
  | some retained => exact retained.winding_zero refines current.proper

end FactorRegion

set_option genInjectivity false in
/-- A protected original factor-root stage and its winding-one region for the original source polynomial.

The source identity, cofactor and coprime result retain their original owners.
The request and selected state use the original root's actual refinement and
cache; the source region consumes that state's factor clearance and the same
retained cofactor clearance.
-/
structure FactorRegion {factor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} (root : CertifiedName track)
    (source cofactor : GaussianPolynomial) (start : Nat) where
  /-- The original coefficient source is the ordered factor/cofactor product. -/
  factorization : Identity.ProductIdentity source factor cofactor
  /-- The original factor and cofactor retain their completed coprime Euclidean result. -/
  coprime : CoprimeCertificate factor cofactor
  /-- The retained cofactor is nonzero, including the constant case. -/
  cofactorNonzero : cofactor.isZero = false
  /-- The actual optional local cofactor presentation used by this same request. -/
  localCofactor : Option (FactorRegion.LocalCofactor cofactor track.initial.box) := none
  /-- The computed positive squared-diagonal request. -/
  targetSq : Coordinate
  /-- The same original coprime certificate determines this request. -/
  targetSq_eq : targetSq = FactorRegion.target root coprime start localCofactor
  /-- The original request is positive. -/
  target_positive : 0 < targetSq
  /-- The actual selected original root stage. -/
  index : Nat
  /-- The original refiner pays this same retained request and start. -/
  index_eq : index = root.approximation.refineIndex start targetSq target_positive
  /-- The selected stage follows the caller's original start. -/
  index_ge : start ≤ index
  /-- The actual retained state read from the original root cache. -/
  current : WindingOneState factor ambient
  /-- The state is the same original cache read at the selected stage. -/
  current_eq : current = root.stateAt index
  /-- The actual retained state meets the original request. -/
  diagonal_lt : current.box.diagonalSq < targetSq
  /-- The original cofactor clearance at this same retained state. -/
  cofactorClearance : Boundary.Basic.BoundaryClearance cofactor current.box
  /-- The cofactor clearance uses the same original coprime margin. -/
  cofactorClearance_bound : cofactorClearance.bound = FactorRegion.cofactorBound (track := track) coprime localCofactor
  /-- The cofactor has zero winding at the same retained state. -/
  cofactor_winding : Winding.Box.Basic.quadrupledBoxWinding cofactor current.box = 0
  /-- The original source's clear region at the same retained factor-root state. -/
  region : Clearance.Box.Region.ClearRegion source ambient
  /-- The source region has exactly the same original cached state box. -/
  region_box : region.box = current.box
  /-- The source clearance is the product of the same retained factor and cofactor bounds. -/
  region_bound : region.clearance.bound = current.clearance.bound * cofactorClearance.bound
  /-- The original source has winding one at that same selected factor-root region. -/
  source_winding : Winding.Box.Basic.quadrupledBoxWinding source region.box = 4

constructive_injectivity FactorRegion

namespace FactorRegion

/-- Construct the original source region from its exact retained maximum-stage refinement.

The payment keeps the original cofactor request and sufficient refiner stage.
Its actual state supplies both clearances, their bounds and source winding;
no original root state is read again.
-/
@[expose] def ofRootWithRefinement {factor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} (root : CertifiedName track) (source cofactor : GaussianPolynomial)
    (sourceNonzero : source.isZero = false)
    (factorization : Identity.ProductIdentity source factor cofactor)
    (coprime : CoprimeCertificate factor cofactor) (start : Nat)
    (requested : Option (LocalCofactor cofactor track.initial.box)) (paid : Refinement root start)
    (request : paid.targetSq = target root coprime start requested)
    (maximum : paid.index = paid.maxIndex) : FactorRegion root source cofactor start := by
  have cofactorNonzero := Identity.right_nonzero sourceNonzero factorization
  let targetSq := paid.targetSq
  have targetPositive : 0 < targetSq := paid.positive
  let index := paid.index
  let current := paid.current
  have diagonal := paid.diagonal_lt.trans_eq request
  have refines := state_refines_of_le track (Nat.zero_le index)
  rewrite [← root.stateAt_eq index, ← paid.current_eq] at refines
  let cofactorClearance := clearanceAt root coprime start requested current refines diagonal
  have cofactorWinding := windingAt root cofactorNonzero coprime start requested current refines diagonal
  let clearance := Boundary.Basic.BoundaryClearance.ofProductIdentity factorization
    current.clearance cofactorClearance
  let region : Clearance.Box.Region.ClearRegion source ambient :=
    { box := current.box
      refinesAmbient := current.refinesAmbient
      proper := current.proper
      clearance := clearance }
  have sourceWinding := Winding.Box.Product.quadrupledBoxWinding_of_productIdentity current.box current.proper
    factorization current.clearance cofactorClearance
  rewrite [current.rawWindingFour, cofactorWinding, Int.add_zero] at sourceWinding
  exact
    { factorization := factorization
      coprime := coprime
      cofactorNonzero := cofactorNonzero
      localCofactor := requested
      targetSq := targetSq
      targetSq_eq := request
      target_positive := targetPositive
      index := index
      index_eq := maximum.trans paid.maxIndex_eq
      index_ge := paid.index_ge
      current := current
      current_eq := paid.current_eq
      diagonal_lt := paid.diagonal_lt
      cofactorClearance := cofactorClearance
      cofactorClearance_bound := clearanceAt_bound root coprime start requested current refines diagonal
      cofactor_winding := cofactorWinding
      region := region
      region_box := rfl
      region_bound := rfl
      source_winding := sourceWinding }

/-- Compute an original-source winding-one region using a retained factorization and coprime cofactor.

The original source's nonzero certificate proves that the cofactor is nonzero.
The source identity and original factor root compute the actual selected
stage. A supplied original local presentation is consumed directly; its
absence retains the complete original global protection construction.
-/
@[expose] def ofRoot {factor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} (root : CertifiedName track) (source cofactor : GaussianPolynomial)
    (sourceNonzero : source.isZero = false)
    (factorization : Identity.ProductIdentity source factor cofactor)
    (coprime : CoprimeCertificate factor cofactor) (start : Nat)
    (requested : Option (LocalCofactor cofactor track.initial.box) := none) :
    FactorRegion root source cofactor start := by
  let targetSq := target root coprime start requested
  have targetPositive : 0 < targetSq := target_pos root coprime start requested
  let index := root.approximation.refineIndex start targetSq targetPositive
  let current := root.stateAt index
  have diagonal := root.stateAt_refineIndex_diagonal_lt start targetSq targetPositive
  exact ofRootWithRefinement root source cofactor sourceNonzero factorization coprime start requested
    (Refinement.atState root start targetSq targetPositive index rfl index
      (root.approximation.refineIndex_ge start targetSq targetPositive) (Nat.le_refl index) current rfl diagonal)
    rfl rfl

/-- An exact retained payment preserves the complete original source-region certificate.

Factorization, cofactor data, request, stage, state, both clearances and the
source region agree together, including each original defining identity.
-/
theorem ofRootWithRefinement_eq {factor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} (root : CertifiedName track) (source cofactor : GaussianPolynomial)
    (sourceNonzero : source.isZero = false) (factorization : Identity.ProductIdentity source factor cofactor)
    (coprime : CoprimeCertificate factor cofactor) (start : Nat)
    (requested : Option (LocalCofactor cofactor track.initial.box))
    (paid : Refinement root start) (request : paid.targetSq = target root coprime start requested)
    (maximum : paid.index = paid.maxIndex) :
    ofRootWithRefinement root source cofactor sourceNonzero factorization coprime start requested
      paid request maximum = ofRoot root source cofactor sourceNonzero factorization coprime start requested := by
  rcases paid with ⟨target, positive, index, maxIndex, maxEq, indexLe, indexGe, current, currentEq, diagonal⟩
  dsimp only [] at request maximum
  cases request
  cases maxEq
  cases maximum
  cases currentEq
  rfl

/-- Restore the complete original source region from one exact maximum-stage state read.

The original global or local cofactor request selects the unchanged sufficient
stage. The supplied reader runs once there, and its actual state or failure
passes through without a default state read.
-/
def ofRootWithStates {m : Type → Type} [Monad m] {factor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} (root : CertifiedName track) (source cofactor : GaussianPolynomial)
    (sourceNonzero : source.isZero = false) (factorization : Identity.ProductIdentity source factor cofactor)
    (coprime : CoprimeCertificate factor cofactor) (start : Nat)
    (requested : Option (LocalCofactor cofactor track.initial.box))
    (states : (index : Nat) → m {current : WindingOneState factor ambient // current = root.stateAt index}) :
    m {certificate : FactorRegion root source cofactor start //
      certificate = ofRoot root source cofactor sourceNonzero factorization coprime start requested} := do
  let targetSq := target root coprime start requested
  have positive := target_pos root coprime start requested
  let index := root.approximation.refineIndex start targetSq positive
  let current ← states index
  have accurate : current.val.box.diagonalSq < targetSq := by
    rewrite [current.property]
    exact root.stateAt_refineIndex_diagonal_lt start targetSq positive
  let paid := Refinement.atState root start targetSq positive index rfl index
    (root.approximation.refineIndex_ge start targetSq positive) (Nat.le_refl index)
    current.val current.property accurate
  return ⟨ofRootWithRefinement root source cofactor sourceNonzero factorization coprime start requested
    paid rfl rfl, ofRootWithRefinement_eq root source cofactor sourceNonzero factorization coprime start requested
      paid rfl rfl⟩

/-- Disabling local cofactor preparation preserves the complete original source-region construction.

The original source factorization, Euclidean certificate, global protection,
selected root cache, both clearances and original region all agree together.
-/
theorem ofRoot_none {factor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} (root : CertifiedName track) (source cofactor : GaussianPolynomial)
    (sourceNonzero : source.isZero = false)
    (factorization : Identity.ProductIdentity source factor cofactor)
    (coprime : CoprimeCertificate factor cofactor) (start : Nat) :
    ofRoot root source cofactor sourceNonzero factorization coprime start none = (by
  have normalizedFactorization :
      Identity.ProductIdentity source.normalize factor cofactor :=
    Identity.factorizationOfCandidateEvals source.normalize factor cofactor
      (fun point _ => (DensePolynomial.eval_normalize source point).trans
        (Identity.eval_factorization factorization point))
  have cofactorNonzero := Identity.right_isZero_false
    ((DensePolynomial.isZero_normalize source).trans sourceNonzero)
    (DensePolynomial.normalize_normalize source) normalizedFactorization
  let targetSq := Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius coprime ambient ^ 2
  have targetPositive : 0 < targetSq := Order.Arithmetic.pow_pos_direct
    (Dense.Gaussian.Coprime.Bounds.Protection.protectionRadius_pos coprime ambient) 2
  let index := root.approximation.refineIndex start targetSq targetPositive
  let current := root.stateAt index
  have diagonal := root.stateAt_refineIndex_diagonal_lt start targetSq targetPositive
  let cofactorClearance := State.WindingOne.Coprime.rightClearance root.degreePositive coprime current diagonal.le
  have cofactorWinding := State.WindingOne.Coprime.right_winding_zero_of_nonzero root.degreePositive
    cofactorNonzero coprime current diagonal.le
  let clearance := Boundary.Basic.BoundaryClearance.ofProductIdentity factorization
    current.clearance cofactorClearance
  let region : Clearance.Box.Region.ClearRegion source ambient :=
    { box := current.box
      refinesAmbient := current.refinesAmbient
      proper := current.proper
      clearance := clearance }
  have sourceWinding := Winding.Box.Product.quadrupledBoxWinding_of_productIdentity current.box current.proper
    factorization current.clearance cofactorClearance
  rewrite [current.rawWindingFour, cofactorWinding, Int.add_zero] at sourceWinding
  exact
    { factorization := factorization
      coprime := coprime
      cofactorNonzero := cofactorNonzero
      targetSq := targetSq
      targetSq_eq := rfl
      target_positive := targetPositive
      index := index
      index_eq := rfl
      index_ge := root.approximation.refineIndex_ge start targetSq targetPositive
      current := current
      current_eq := rfl
      diagonal_lt := diagonal
      cofactorClearance := cofactorClearance
      cofactorClearance_bound := rfl
      cofactor_winding := cofactorWinding
      region := region
      region_box := rfl
      region_bound := rfl
      source_winding := sourceWinding }

    ) := by
  rfl

/-- The same actual optional local cofactor cache is retained by original region construction. -/
theorem ofRoot_localCofactor {factor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} (root : CertifiedName track) (source cofactor : GaussianPolynomial)
    (sourceNonzero : source.isZero = false)
    (factorization : Identity.ProductIdentity source factor cofactor)
    (coprime : CoprimeCertificate factor cofactor) (start : Nat)
    (requested : Option (LocalCofactor cofactor track.initial.box)) :
    (ofRoot root source cofactor sourceNonzero factorization coprime start requested).localCofactor = requested := rfl

/-- A retained local cofactor presentation pays exactly the original requested starting stage. -/
theorem ofRoot_some_index {factor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} (root : CertifiedName track) (source cofactor : GaussianPolynomial)
    (sourceNonzero : source.isZero = false)
    (factorization : Identity.ProductIdentity source factor cofactor)
    (coprime : CoprimeCertificate factor cofactor) (start : Nat)
    (requested : LocalCofactor cofactor track.initial.box) :
    (ofRoot root source cofactor sourceNonzero factorization coprime start (some requested)).index = start := by
  change root.approximation.refineIndex start (root.approximation.radiusSq start + 1) _ = start
  apply root.refineIndex_eq_of_lt
  have accurate := Fraction.Order.Arithmetic.add_lt_add_left_direct
    (show (0 : Coordinate) < 1 by decide) (root.approximation.radiusSq start)
  rewrite [Fraction.Field.add_comm (root.approximation.radiusSq start) 0, Fraction.Field.zero_add] at accurate
  exact accurate

/-- The local request retains the original root cache read at exactly the caller's starting stage. -/
theorem ofRoot_some_current {factor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} (root : CertifiedName track) (source cofactor : GaussianPolynomial)
    (sourceNonzero : source.isZero = false)
    (factorization : Identity.ProductIdentity source factor cofactor)
    (coprime : CoprimeCertificate factor cofactor) (start : Nat)
    (requested : LocalCofactor cofactor track.initial.box) :
    (ofRoot root source cofactor sourceNonzero factorization coprime start (some requested)).current =
      root.stateAt start := by
  rewrite [(ofRoot root source cofactor sourceNonzero factorization coprime start (some requested)).current_eq,
    ofRoot_some_index]
  rfl

/-- Every later original cached factor-root state meets the same retained cofactor protection budget. -/
theorem later_diagonal {factor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} {root : CertifiedName track}
    {source cofactor : GaussianPolynomial} {start : Nat}
    (certificate : FactorRegion root source cofactor start) {later : Nat} (order : certificate.index ≤ later) :
    (root.stateAt later).box.diagonalSq <
      target root certificate.coprime start certificate.localCofactor := by
  have originalOrder : root.approximation.refineIndex start certificate.targetSq
      certificate.target_positive ≤ later := by
    rewrite [← certificate.index_eq]
    exact order
  have diagonal := root.stateAt_diagonal_lt_of_refineIndex_le start certificate.targetSq
    certificate.target_positive originalOrder
  rewrite [certificate.targetSq_eq] at diagonal
  exact diagonal

/-- Build a later original-source region from the actual authenticated factor state.

The original factorization, local cofactor and paid protection stage are
retained. Both clearance factors consume the supplied state at that same
later index rather than performing another root-state read.
-/
@[expose] def regionAtFromState {factor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} {root : CertifiedName track}
    {source cofactor : GaussianPolynomial} {start : Nat}
    (certificate : FactorRegion root source cofactor start) (later : Nat) (order : certificate.index ≤ later)
    (current : WindingOneState factor ambient) (same : current = root.stateAt later) :
    Clearance.Box.Region.ClearRegion source ambient := by
  have refines := state_refines_of_le track (Nat.zero_le later)
  rewrite [← root.stateAt_eq later, ← same] at refines
  have diagonal : current.box.diagonalSq < target root certificate.coprime start certificate.localCofactor := by
    rewrite [same]
    exact certificate.later_diagonal order
  let cofactorClearance := clearanceAt root certificate.coprime start certificate.localCofactor
    current refines diagonal
  exact
    { box := current.box
      refinesAmbient := current.refinesAmbient
      proper := current.proper
      clearance := Boundary.Basic.BoundaryClearance.ofProductIdentity certificate.factorization
        current.clearance cofactorClearance }

/-- Construct the original source's clear region at a later read from the same original factor-root cache. -/
@[expose] def regionAt {factor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} {root : CertifiedName track}
    {source cofactor : GaussianPolynomial} {start : Nat}
    (certificate : FactorRegion root source cofactor start) (later : Nat) (order : certificate.index ≤ later) :
    Clearance.Box.Region.ClearRegion source ambient :=
  regionAtFromState certificate later order (root.stateAt later) rfl

/-- A supplied exact state preserves the complete original later source region. -/
theorem regionAtFromState_eq {factor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} {root : CertifiedName track}
    {source cofactor : GaussianPolynomial} {start : Nat}
    (certificate : FactorRegion root source cofactor start) (later : Nat) (order : certificate.index ≤ later)
    (current : WindingOneState factor ambient) (same : current = root.stateAt later) :
    certificate.regionAtFromState later order current same = certificate.regionAt later order := by
  cases same
  rfl

/-- The later original-source region retains precisely the same original cache-read box. -/
theorem regionAt_box {factor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} {root : CertifiedName track}
    {source cofactor : GaussianPolynomial} {start : Nat}
    (certificate : FactorRegion root source cofactor start) (later : Nat) (order : certificate.index ≤ later) :
    (certificate.regionAt later order).box = (root.stateAt later).box := rfl

/-- Every later original factor-root region retains winding one for its original source polynomial. -/
theorem regionAt_winding {factor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} {root : CertifiedName track}
    {source cofactor : GaussianPolynomial} {start : Nat}
    (certificate : FactorRegion root source cofactor start) (later : Nat) (order : certificate.index ≤ later) :
    Winding.Box.Basic.quadrupledBoxWinding source (certificate.regionAt later order).box = 4 := by
  let current := root.stateAt later
  have diagonal := certificate.later_diagonal order
  have refines := state_refines_of_le track (Nat.zero_le later)
  rewrite [← root.stateAt_eq later] at refines
  let cofactorClearance := clearanceAt root certificate.coprime start certificate.localCofactor
    current refines diagonal
  have cofactorWinding := windingAt root certificate.cofactorNonzero certificate.coprime start
    certificate.localCofactor current refines diagonal
  have sourceWinding := Winding.Box.Product.quadrupledBoxWinding_of_productIdentity current.box current.proper
    certificate.factorization current.clearance cofactorClearance
  rewrite [current.rawWindingFour, cofactorWinding, Int.add_zero] at sourceWinding
  exact sourceWinding

/-- The later region built from its actual retained factor state has original source winding one. -/
theorem regionAtFromState_winding {factor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} {root : CertifiedName track}
    {source cofactor : GaussianPolynomial} {start : Nat}
    (certificate : FactorRegion root source cofactor start) (later : Nat) (order : certificate.index ≤ later)
    (current : WindingOneState factor ambient) (same : current = root.stateAt later) :
    Winding.Box.Basic.quadrupledBoxWinding source
      (certificate.regionAtFromState later order current same).box = 4 := by
  rewrite [certificate.regionAtFromState_eq later order current same]
  exact certificate.regionAt_winding later order

/-- Compare the two original cached channels inside the same original-source winding-one region.

The checked factorization supplies source winding one on every sufficiently
late original factor box. Finite clear-region counting excludes separation
from the original source box; actual cache reads and each original refiner
then compute the all-start comparison without replacing either input channel.
-/
def compare_in_region {source factor cofactor : GaussianPolynomial} {sourceAmbient factorAmbient containerAmbient : Box}
    {sourceTrack : WindingOneTrack source sourceAmbient} {factorTrack : WindingOneTrack factor factorAmbient}
    {factorRoot : CertifiedName factorTrack} {start : Nat}
    (certificate : FactorRegion factorRoot source cofactor start)
    (input : FTA.Squarefree.Input source) (sourceRoot : CertifiedName sourceTrack)
    (container : Clearance.Box.Region.ClearRegion source containerAmbient)
    (one : Winding.Box.Basic.quadrupledBoxWinding source container.box = 4)
    (sourceNested : sourceTrack.initial.box.Refines container.box)
    (floor : Nat) (protectedFloor : certificate.index ≤ floor)
    (factorNested : (factorRoot.stateAt floor).box.Refines container.box) :
    Equivalence.Equivalent sourceRoot.approximation factorRoot.approximation where
  compare firstStart secondStart target positive := by
    let quarter := target / 4
    have quarterPositive : 0 < quarter := Fraction.Order.Field.div_pos_direct positive (by decide)
    let firstIndex := sourceRoot.approximation.refineIndex firstStart quarter quarterPositive
    let secondIndex := factorRoot.approximation.refineIndex (max secondStart floor) quarter quarterPositive
    have startMax : secondStart ≤ max secondStart floor := by
      rewrite [Purelib.Data.Nat.Order.max_eq_natMax]
      exact Purelib.Data.Nat.Order.le_max_left _ _
    have protectedMax : floor ≤ max secondStart floor := by
      rewrite [Purelib.Data.Nat.Order.max_eq_natMax]
      exact Purelib.Data.Nat.Order.le_max_right _ _
    have second_ge : secondStart ≤ secondIndex :=
      startMax.trans (factorRoot.approximation.refineIndex_ge _ _ _)
    have floor_ge : floor ≤ secondIndex :=
      protectedMax.trans (factorRoot.approximation.refineIndex_ge _ _ _)
    exact
      { leftIndex := firstIndex
        rightIndex := secondIndex
        left_ge := sourceRoot.approximation.refineIndex_ge _ _ _
        right_ge := second_ge
        close := by
          intro firstLater secondLater firstOrder secondOrder
          let firstState := sourceRoot.stateAt firstLater
          let secondState := factorRoot.stateAt secondLater
          let factorRegion := certificate.regionAt secondLater (protectedFloor.trans (floor_ge.trans secondOrder))
          have firstNested := state_refines_of_le sourceTrack (Nat.zero_le firstLater)
          have secondNested := state_refines_of_le factorTrack (floor_ge.trans secondOrder)
          rewrite [← sourceRoot.stateAt_eq firstLater] at firstNested
          rewrite [← factorRoot.stateAt_eq secondLater, ← factorRoot.stateAt_eq floor] at secondNested
          let left : Clearance.Box.Region.ClearRegion source containerAmbient :=
            { box := firstState.box
              refinesAmbient := (firstNested.trans sourceNested).trans container.refinesAmbient
              proper := firstState.proper
              clearance := firstState.clearance }
          let right : Clearance.Box.Region.ClearRegion source containerAmbient :=
            { box := factorRegion.box
              refinesAmbient := (secondNested.trans factorNested).trans container.refinesAmbient
              proper := factorRegion.proper
              clearance := factorRegion.clearance }
          have leftPositive : 0 < Winding.Box.Basic.quadrupledBoxWinding source left.box := by
            rewrite [firstState.rawWindingFour]
            decide
          have rightPositive : 0 < Winding.Box.Basic.quadrupledBoxWinding source right.box := by
            rewrite [certificate.regionAt_winding secondLater (protectedFloor.trans (floor_ge.trans secondOrder))]
            decide
          have notSeparated := Winding.Box.Region.not_separated_in_winding_one_region
            input container left right one
            leftPositive rightPositive (firstNested.trans sourceNested)
            (secondNested.trans factorNested)
          let point := Box.overlapPoint firstState.box secondState.box
          have inside := Box.contains_overlapPoint_of_not_separated notSeparated
          have firstBound := firstState.box.normSq_sub_le_diagonalSq firstState.box.contains_anchor inside.1
          have secondBound := secondState.box.normSq_sub_le_diagonalSq inside.2 secondState.box.contains_anchor
          have firstDiagonal := sourceRoot.stateAt_diagonal_lt_of_refineIndex_le firstStart quarter
            quarterPositive firstOrder
          have secondDiagonal := factorRoot.stateAt_diagonal_lt_of_refineIndex_le
            (max secondStart floor) quarter quarterPositive secondOrder
          rewrite [sourceRoot.sample_stateAt firstLater, factorRoot.sample_stateAt secondLater]
          calc
            normSq (firstState.box.anchor - secondState.box.anchor) ≤
                2 * (normSq (firstState.box.anchor - point) + normSq (point - secondState.box.anchor)) :=
              Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
            _ ≤ 2 * (firstState.box.diagonalSq + secondState.box.diagonalSq) :=
              Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (Order.Arithmetic.add_le_add_direct firstBound secondBound) (by decide)
            _ < 2 * (quarter + quarter) := Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
              (Order.Arithmetic.add_lt_add_direct firstDiagonal secondDiagonal)
            _ = target := by
              dsimp only [quarter]
              rewrite [Purelib.Data.Rat.Bounds.Quarter.two_quarters target, Fraction.Field.mul_comm]
              exact Purelib.Data.Rat.Bounds.Quarter.half_mul_two target }

/-- Compare the original channels in an independently indexed original-source container.

Only the proved coefficient equality is transported. The same original
source root and factor root consume their retained caches, the actual
container winding, and their supplied containment certificates.
-/
def compare_in_region_of_eq {source originalSource factor cofactor : GaussianPolynomial}
    {sourceAmbient factorAmbient containerAmbient : Box}
    {sourceTrack : WindingOneTrack originalSource sourceAmbient}
    {factorTrack : WindingOneTrack factor factorAmbient} {factorRoot : CertifiedName factorTrack} {start : Nat}
    (certificate : FactorRegion factorRoot source cofactor start) (same : source = originalSource)
    (input : FTA.Squarefree.Input originalSource) (sourceRoot : CertifiedName sourceTrack)
    (container : Clearance.Box.Region.ClearRegion originalSource containerAmbient)
    (one : Winding.Box.Basic.quadrupledBoxWinding originalSource container.box = 4)
    (sourceNested : sourceTrack.initial.box.Refines container.box)
    (floor : Nat) (protectedFloor : certificate.index ≤ floor)
    (factorNested : (factorRoot.stateAt floor).box.Refines container.box) :
    Equivalence.Equivalent sourceRoot.approximation factorRoot.approximation := by
  cases same
  exact certificate.compare_in_region input sourceRoot container one sourceNested floor protectedFloor factorNested

/-- Compare both original caches at a protected factor state inside the source root's original winding-one owner. -/
def compare {source factor cofactor : GaussianPolynomial} {sourceAmbient factorAmbient : Box}
    {sourceTrack : WindingOneTrack source sourceAmbient} {factorTrack : WindingOneTrack factor factorAmbient}
    {factorRoot : CertifiedName factorTrack} {start : Nat}
    (certificate : FactorRegion factorRoot source cofactor start)
    (input : FTA.Squarefree.Input source) (sourceRoot : CertifiedName sourceTrack)
    (nested : certificate.current.box.Refines sourceTrack.initial.box) :
    Equivalence.Equivalent sourceRoot.approximation factorRoot.approximation :=
  let container : Clearance.Box.Region.ClearRegion source sourceAmbient :=
    { box := sourceTrack.initial.box
      refinesAmbient := sourceTrack.initial.refinesAmbient
      proper := sourceTrack.initial.proper
      clearance := sourceTrack.initial.clearance }
  certificate.compare_in_region input sourceRoot container sourceTrack.initial.rawWindingFour
    (Box.refines_refl _) certificate.index (Nat.le_refl _) (by
      rewrite [← certificate.current_eq]
      exact nested)

/-- Either actual initial-box containment direction between the same original source root and factor-region cache.

The sum retains which finite endpoint check succeeded. Both sides are the
original box-refinement propositions, with no operational root-equivalence premise.
-/
abbrev InitialNesting {source originalSource factor cofactor : GaussianPolynomial}
    {sourceAmbient factorAmbient : Box}
    {sourceTrack : WindingOneTrack originalSource sourceAmbient}
    {factorTrack : WindingOneTrack factor factorAmbient} {factorRoot : CertifiedName factorTrack} {start : Nat}
    (certificate : FactorRegion factorRoot source cofactor start) (_sourceRoot : CertifiedName sourceTrack) :=
  Sum (PLift (certificate.current.box.Refines sourceTrack.initial.box))
    (PLift (sourceTrack.initial.box.Refines certificate.current.box))

/-- Inspect both original initial-containment directions, preferring the protected factor box inside the source.

The supplied region and source track determine both exact comparisons. A miss
retains no containment claim; a success carries the original directional witness.
-/
@[expose] def initialNesting? {source originalSource factor cofactor : GaussianPolynomial}
    {sourceAmbient factorAmbient : Box}
    {sourceTrack : WindingOneTrack originalSource sourceAmbient}
    {factorTrack : WindingOneTrack factor factorAmbient} {factorRoot : CertifiedName factorTrack} {start : Nat}
    (certificate : FactorRegion factorRoot source cofactor start) (sourceRoot : CertifiedName sourceTrack) :
    Option (certificate.InitialNesting sourceRoot) :=
  letI : Decidable (certificate.current.box.Refines sourceTrack.initial.box) :=
    Box.refinesDecidable certificate.current.box sourceTrack.initial.box
  letI : Decidable (sourceTrack.initial.box.Refines certificate.current.box) :=
    Box.refinesDecidable sourceTrack.initial.box certificate.current.box
  if forward : certificate.current.box.Refines sourceTrack.initial.box then
    some (.inl ⟨forward⟩)
  else if backward : sourceTrack.initial.box.Refines certificate.current.box then
    some (.inr ⟨backward⟩)
  else none

/-- Compare with an actual original source-root owner transported only along proved polynomial equality.

The equality changes the source coefficient index. The same complete source
root, factor root, cache reads and container drive the original comparison.
It does not identify independently retained root or Sidecar parents.
-/
def compare_of_eq {source originalSource factor cofactor : GaussianPolynomial}
    {sourceAmbient factorAmbient : Box}
    {sourceTrack : WindingOneTrack originalSource sourceAmbient}
    {factorTrack : WindingOneTrack factor factorAmbient} {factorRoot : CertifiedName factorTrack} {start : Nat}
    (certificate : FactorRegion factorRoot source cofactor start) (same : source = originalSource)
    (input : FTA.Squarefree.Input originalSource) (sourceRoot : CertifiedName sourceTrack)
    (nested : certificate.InitialNesting sourceRoot) :
    Equivalence.Equivalent sourceRoot.approximation factorRoot.approximation := by
  cases same
  cases nested with
  | inl forward => exact certificate.compare input sourceRoot forward.down
  | inr backward =>
      exact certificate.compare_in_region input sourceRoot certificate.region certificate.source_winding
        (by
          rewrite [certificate.region_box]
          exact backward.down)
        certificate.index (Nat.le_refl _) (by
          rewrite [← certificate.current_eq, certificate.region_box]
          exact Box.refines_refl _)

/-- The original source and protected factor names agree through their actual cached all-start comparison. -/
def equivalent {source factor cofactor : GaussianPolynomial} {sourceAmbient factorAmbient : Box}
    {sourceTrack : WindingOneTrack source sourceAmbient} {factorTrack : WindingOneTrack factor factorAmbient}
    {factorRoot : CertifiedName factorTrack} {start : Nat}
    (certificate : FactorRegion factorRoot source cofactor start)
    (input : FTA.Squarefree.Input source) (sourceRoot : CertifiedName sourceTrack)
    (nested : certificate.current.box.Refines sourceTrack.initial.box) :
    Equivalence.NamedEquivalent sourceRoot.value.name factorRoot.value.name := by
  rewrite [sourceRoot.value_approximation, factorRoot.value_approximation]
  exact (certificate.compare input sourceRoot nested).toNamed

set_option genInjectivity false in
/-- A retained source-polynomial extraction and its original-channel comparison at the same factor region.

The source root is indexed by the actual extracted track inside this exact
original-source region. Its own cached approximation is built once, and the
comparison retains that same source root and the original factor-root channel.
-/
structure Realization {source factor cofactor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} {factorRoot : CertifiedName track} {start : Nat}
    (certificate : FactorRegion factorRoot source cofactor start) where
  /-- The actual finite extraction from the same retained source region. -/
  extraction : Exact.Extraction.RegionExtraction source ambient certificate.region
  /-- The original source's cached root on the same actual extracted track. -/
  root : CertifiedName extraction.track
  /-- The two original root channels agree through the same retained source region. -/
  equivalent : Equivalence.NamedEquivalent root.value.name factorRoot.value.name

constructive_injectivity Realization

/-- Extract and retain the source's own root program at a protected original factor-root region.

The source coefficient data determines its finite extraction and refinement
program. Its cached root is constructed once. Winding one of the same retained
source region then supplies the original-channel comparison to the factor root;
the new source program does not copy the factor samples.
-/
@[expose] def realize {source factor cofactor : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack factor ambient} {factorRoot : CertifiedName track} {start : Nat}
    (certificate : FactorRegion factorRoot source cofactor start) (input : FTA.Squarefree.Input source) :
    Realization certificate := by
  have positive : 0 < Winding.Box.Basic.quadrupledBoxWinding source certificate.region.box := by
    rewrite [certificate.source_winding]
    decide
  let extraction := Exact.Extraction.extractRegion input.degreeAtLeastTwo input.squarefree input.elimination
    certificate.region positive
  let root := certifiedName extraction.track input.degreePositive
  have factorNested : certificate.current.box.Refines certificate.region.box := by
    rewrite [certificate.region_box]
    exact Box.refines_refl _
  let comparison := certificate.compare_in_region input root certificate.region certificate.source_winding
    (Box.Refinement.StrictInterior.refines extraction.centerStrict) certificate.index (Nat.le_refl _) (by
      rewrite [← certificate.current_eq]
      exact factorNested)
  have equivalent : Equivalence.NamedEquivalent root.value.name factorRoot.value.name := by
    rewrite [root.value_approximation, factorRoot.value_approximation]
    exact comparison.toNamed
  exact
    { extraction := extraction
      root := root
      equivalent := equivalent }

end FactorRegion

end Purelib.Riemann.RootContinuation.CoherentRoot

end
