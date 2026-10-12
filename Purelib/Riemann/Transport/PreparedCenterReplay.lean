module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Algebra.Field.ExplicitField
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.Request.Common
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Branches.SquareRootSheets

public import Purelib.Riemann.Integration.PreparedConstantModels

@[expose] public section

/-!
# Recovering the finite state of a prepared center

The root-refinement cursor is determined by finite numeric metadata, not by
the samples chosen by the root track.  Recovering this cursor does not by
itself recover a sample, its ownership, or the canonical center value.
-/

namespace Purelib.Riemann.Transport.PreparedCenterReplay

open Purelib.Riemann.Branches Purelib.Riemann.Integration

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)

section
open Purelib.Data
/-- The exact rational carrier of the retained cursor bounds. -/
abbrev Coordinate := Rat.Fraction.Rational
/-- The exact Gaussian rational carrier of the retained center data. -/
abbrev Gaussian := Gaussian.Basic.Canonical
end

open Purelib.Geometry.Rational (Box) in
/-- The rational box type of the original root track. -/
abbrev Box := Purelib.Geometry.Rational.Box

set_option genInjectivity false in
/-- Finite numerical inputs determining the prepared denominator cursor.

These values encode the original polynomial parameter, boxes and requested bounds; source association is separate
evidence tying this record to a prepared edge. -/
structure Metadata where
  /-- The polynomial value at the original center point. -/ parameter : Gaussian
  /-- The ambient box of the original query owner. -/ rootAmbient : Box
  /-- The initial box of the original query owner's root track. -/ rootBox : Box
  /-- The exact differential numerator at the original center point. -/ numerator : Gaussian
  /-- The retained squared-norm bound on the differential numerator. -/ numeratorBound : Coordinate
  /-- The positive residual target of the original prepared edge. -/ rootResidualTarget : Coordinate
  /-- The original coefficient-reading error target. -/ readingTarget : Coordinate

constructive_injectivity Metadata

open Purelib.Polynomial.Dense.Gaussian.Bounds in
open Purelib.Polynomial.Power.Gaussian in
open Purelib.Riemann in
/-- The root-polynomial Lipschitz bound times the initial box's squared diagonal. -/
def Metadata.residualScale (data : Metadata) : Coordinate :=
  Box.denseLipschitzBound
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial data.parameter RootContinuation.SquareRootDegree.degreeTwo)
    data.rootAmbient * data.rootBox.diagonalSq

open Purelib.Approximation.Rational.Geometric in
open Purelib.Riemann in
/-- The first quarter-refinement index meeting the sheet residual target. -/
def Metadata.baseIndex (data : Metadata) : Nat :=
  Search.firstQuarterBelow data.residualScale 0
    (Branches.SquareRootSheets.residualTarget data.parameter)

open Purelib.Approximation.Rational.Geometric in
/-- The first quarter-refinement index meeting the retained residual target. -/
def Metadata.residualIndex (data : Metadata) : Nat :=
  Search.firstQuarterBelow data.residualScale 0 data.rootResidualTarget

open Purelib.Approximation.Rational.Geometric in
open Purelib.Riemann in
/-- The first admissible diameter index after both residual requirements are met. -/
def Metadata.preparedIndex (data : Metadata) : Nat :=
  Search.firstQuarterBelow data.rootBox.diagonalSq
    (max data.baseIndex data.residualIndex)
    (Branches.SquareRootSheets.sampleNormLower data.parameter / 12)

open Purelib.Riemann in
/-- The coefficient input tolerance paid by the retained numerator and root bounds. -/
def Metadata.inputTarget (data : Metadata) : Coordinate :=
  let lower := Branches.SquareRootSheets.sampleNormLower data.parameter / 8
  (data.readingTarget * (lower * lower)) /
    (4 * (data.numeratorBound + data.rootAmbient.normSqBound + 1))

open Purelib.Approximation.Rational.Geometric in
open Purelib.Approximation.Rational.Request in
open Purelib.Riemann in
/-- The exact denominator cursor meeting the combined coefficient and sheet tolerances. -/
def Metadata.readingIndex (data : Metadata) : Nat :=
  Search.firstQuarterBelow data.rootBox.diagonalSq
    (max data.baseIndex data.preparedIndex)
    (Common.commonTarget data.inputTarget
      (Branches.SquareRootSheets.sampleNormLower data.parameter / 12))

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Data.Gaussian.Norm in
/-- Extract the original finite numerical inputs from a prepared edge. -/
def metadata (edge : PreparedEdge curve differential) : Metadata where
  parameter := curve.polynomial.eval (edge.segment.pointAt
    (PreparedSheetContinuation.parameterAt edge.left edge.request 0))
  rootAmbient := (edge.directQueryOwner 0 edge.baseInside).ambient
  rootBox := (edge.directQueryOwner 0 edge.baseInside).track.initial.box
  numerator := edge.point 0 ^ differential.exponent
  numeratorBound := Basic.normSq (edge.point 0) ^
    differential.exponent
  rootResidualTarget := edge.rootResidualTarget
  readingTarget := edge.readingTarget

open Purelib.Approximation.Gaussian.Name.Coherent in
open Purelib.Approximation.Rational.Geometric in
/-- The metadata cursor equals the original coefficient state's denominator cursor. -/
theorem readingIndex_eq (edge : PreparedEdge curve differential) :
    (metadata edge).readingIndex = (edge.readingState 0 edge.baseInside).2.source := by
  unfold PreparedEdge.readingState
  change (metadata edge).readingIndex =
    Search.firstQuarterBelow _ _ _
  simp only [Metadata.readingIndex, Metadata.inputTarget, Metadata.preparedIndex,
    Metadata.baseIndex, Metadata.residualIndex, Metadata.residualScale, metadata,
    Power.namedPower_exact_centerBound]
  rfl

section
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
/-- Reconstruct the unique finite state of an exact Gaussian power.

Every recursive component is a unit state, so construction evaluates neither the power nor a process witness. -/
def powerState (point : Gaussian) : (exponent : Nat) →
    (Power.namedPower
      (Coherence.exact point) exponent).name.process.State
  | 0 => ()
  | exponent + 1 => (powerState point exponent, ())

/-- Every finite state of an exact Gaussian power equals the reconstructed unit state. -/
theorem powerState_eq (point : Gaussian) (exponent : Nat)
    (state : (Power.namedPower
      (Coherence.exact point) exponent).name.process.State) :
    powerState point exponent = state := by
  induction exponent with
  | zero => cases state; rfl
  | succ exponent ih =>
      rcases state with ⟨left, right⟩
      cases right
      exact congrArg (fun value => (value, ())) (ih left)

end

/-- Equal denominator cursors determine equal complete coefficient states.

The numerator state is unique and the denominator's lower-bound certificate is proof data. -/
theorem state_eq_of_source_eq (edge : PreparedEdge curve differential)
    (left right : (edge.coefficient 0 edge.baseInside).name.process.State)
    (same : left.2.source = right.2.source) : left = right := by
  rcases left with ⟨leftPower, leftRoot⟩
  rcases right with ⟨rightPower, rightRoot⟩
  apply Prod.ext
  · exact (powerState_eq (edge.point 0) differential.exponent leftPower).symm.trans
      (powerState_eq (edge.point 0) differential.exponent rightPower)
  · cases leftRoot
    cases rightRoot
    cases same
    rfl

/-- Restore the original coefficient state from a cursor and its exact source equation.

The whole-ball lower bound is transported from the original state in a proof field; executable data consists of the
supplied cursor and unique power state. -/
def stateOfIndex (edge : PreparedEdge curve differential) (index : Nat)
    (same : index = (edge.readingState 0 edge.baseInside).2.source) :
    (edge.coefficient 0 edge.baseInside).name.process.State :=
  (powerState (edge.point 0) differential.exponent,
    ⟨index, by rw [same]; exact (edge.readingState 0 edge.baseInside).2.wholeBallLower⟩)

/-- Restoration from an equal cursor returns the exact original reading state. -/
theorem stateOfIndex_eq (edge : PreparedEdge curve differential) (index : Nat)
    (same : index = (edge.readingState 0 edge.baseInside).2.source) :
    stateOfIndex edge index same = edge.readingState 0 edge.baseInside :=
  state_eq_of_source_eq edge _ _ same

/-- Reconstruct the original finite state from source-associated metadata.

The supplied equality to the edge's metadata identifies the denominator cursor and preserves the full coefficient state.
-/
def restoreState (edge : PreparedEdge curve differential) (data : Metadata)
    (associated : data = metadata edge) :
    (edge.coefficient 0 edge.baseInside).name.process.State :=
  stateOfIndex edge data.readingIndex
    ((congrArg Metadata.readingIndex associated).trans (readingIndex_eq edge))

/-- Source-associated metadata restores the exact original reading state. -/
theorem restoreState_eq (edge : PreparedEdge curve differential) (data : Metadata)
    (associated : data = metadata edge) :
    restoreState edge data associated = edge.readingState 0 edge.baseInside :=
  stateOfIndex_eq edge _ _

/-- The actual denominator witness selected by the original reading state. -/
def denominator (edge : PreparedEdge curve differential) : Gaussian :=
  ((edge.sheetValue 0 edge.baseInside).value.name.process.witness
    (edge.readingState 0 edge.baseInside).2).val

/-- The root-track sample index after applying the original base-index floor. -/
def Metadata.sampleIndex (data : Metadata) : Nat := max data.baseIndex data.readingIndex

open Purelib.Riemann in
/-- The original denominator witness is the anchor of the metadata-selected root box. -/
theorem denominator_eq_anchor (edge : PreparedEdge curve differential) :
    denominator edge =
      (RootContinuation.CoherentRoot.state (edge.directQueryOwner 0 edge.baseInside).track
        (metadata edge).sampleIndex).box.anchor := by
  change (RootContinuation.CertifiedSquareRoot.approximation
    (edge.directQueryOwner 0 edge.baseInside).track).sample
      (edge.readingState 0 edge.baseInside).2.source = _
  rw [RootContinuation.CertifiedSquareRoot.approximation_sample, ← readingIndex_eq]
  rfl

set_option genInjectivity false in
/-- A saved denominator value with equality to the original selected witness.

The equality retains the actual source association required for exact center restoration, including the original sample
choice. -/
structure Sample (edge : PreparedEdge curve differential) where
  /-- The saved exact Gaussian denominator value. -/ value : Gaussian
  /-- The saved value equals the original reading state's selected witness. -/ eq_original : value = denominator edge

constructive_injectivity Sample

open Purelib.Riemann in
/-- Restore the denominator witness from a box tied to the exact original root-track state. -/
def Sample.ofBox (edge : PreparedEdge curve differential) (box : Box)
    (associated : box =
      (RootContinuation.CoherentRoot.state (edge.directQueryOwner 0 edge.baseInside).track
        (metadata edge).sampleIndex).box) : Sample edge :=
  ⟨box.anchor, (congrArg (fun value : Box => value.anchor) associated).trans
    (denominator_eq_anchor edge).symm⟩

open Purelib.Data.Gaussian.Norm in
/-- The source-associated denominator witness is nonzero. -/
theorem Sample.nonzero {edge : PreparedEdge curve differential} (sample : Sample edge) :
    sample.value ≠ 0 := by
  have possible : (edge.sheetValue 0 edge.baseInside).value.name.process.Possible
      (edge.readingState 0 edge.baseInside).2 sample.value := by
    rw [sample.eq_original]
    exact ((edge.sheetValue 0 edge.baseInside).value.name.process.witness
      (edge.readingState 0 edge.baseInside).2).property
  let apart := (edge.sheetValue 0 edge.baseInside).apart.certificate
  have positive : 0 < Basic.normSq sample.value :=
    apart.positive.trans_le (apart.lower _
      ((edge.sheetValue 0 edge.baseInside).value.name.process.possible_inside possible))
  intro zero
  rw [zero, Basic.normSq_zero] at positive
  exact (lt_irrefl _ positive)

set_option genInjectivity false in
/-- A numerical cursor or quotient check that failed with explicit unequal values. -/
inductive Invalidity where
  /-- The saved cursor differs from the cursor computed from the retained metadata. -/ | cursor (saved expected : Nat)
    (failed : saved ≠ expected)
  /-- The supplied product differs from the expected exact numerator. -/ | quotient (saved expected : Gaussian) (failed
    : saved ≠ expected)

constructive_injectivity Invalidity

/-- Check a saved cursor against the metadata computation, returning equality or explicit invalidity. -/
def checkIndex (data : Metadata) (saved : Nat) :
    Except Invalidity { index : Nat // index = data.readingIndex } :=
  let expected := data.readingIndex
  if same : saved = expected then .ok ⟨saved, same⟩
  else .error (.cursor saved expected same)

/-- Install the checked state, sample and quotient in the original center representation.

The numerical values are retained in constant thunks; state association, possible-value evidence and the radius bound
occur only in proof positions. -/
def restoreCenter (edge : PreparedEdge curve differential) (data : Metadata)
    (associated : data = metadata edge) (index : { n : Nat // n = data.readingIndex })
    (sample : Sample edge)
    (value : Gaussian)
    (quotient : value = edge.point 0 ^ differential.exponent / sample.value) :
    PreparedEdge.CenterState edge :=
  let same := index.property.trans
    ((congrArg Metadata.readingIndex associated).trans (readingIndex_eq edge))
  PreparedEdge.CenterState.ofCertified edge (stateOfIndex edge index.val same)
    value sample.value
    (by
      rw [stateOfIndex_eq, sample.eq_original]
      exact ((edge.sheetValue 0 edge.baseInside).value.name.process.witness
        (edge.readingState 0 edge.baseInside).2).property)
    quotient
    (by rw [stateOfIndex_eq]; exact fun possible => possible)
    (by rw [stateOfIndex_eq]; exact edge.reading_radius_lt 0 edge.baseInside)

/-- Certified state and sample identities give the exact canonical center.

The equality preserves both constant-closure thunks and uses no function extensionality. -/
private theorem ofCertified_eq (edge : PreparedEdge curve differential)
    (state : (edge.coefficient 0 edge.baseInside).name.process.State)
    (stateEq : state = edge.readingState 0 edge.baseInside)
    (value sample : Gaussian)
    (possible : (edge.sheetValue 0 edge.baseInside).value.name.process.Possible state.2 sample)
    (quotient : value = edge.point 0 ^ differential.exponent / sample)
    (persists : ∀ {v}, (edge.coefficient 0 edge.baseInside).name.process.Possible state v →
      (edge.coefficient 0 edge.baseInside).name.process.Possible
        (edge.readingState 0 edge.baseInside) v)
    (fine : ((edge.coefficient 0 edge.baseInside).name.process.ball state).radiusSq < edge.readingTarget)
    (sampleEq : sample = denominator edge) :
    PreparedEdge.CenterState.ofCertified edge state value sample possible quotient persists fine =
      PreparedEdge.CenterState.canonical edge := by
  cases stateEq
  cases sampleEq
  have valueEq : value = (PreparedEdge.CenterState.canonical edge).value :=
    quotient.trans (PreparedEdge.CenterState.canonical edge).cachedValue_eq_power_div_denominator.symm
  cases valueEq
  rfl

/-- Restoring the associated state, sample and quotient yields the original canonical center. -/
theorem restoreCenter_eq (edge : PreparedEdge curve differential) (data : Metadata)
    (associated : data = metadata edge) (index : { n : Nat // n = data.readingIndex })
    (sample : Sample edge)
    (value : Gaussian)
    (quotient : value = edge.point 0 ^ differential.exponent / sample.value) :
    restoreCenter edge data associated index sample value quotient =
      PreparedEdge.CenterState.canonical edge := by
  unfold restoreCenter
  apply ofCertified_eq
  · exact stateOfIndex_eq edge _ _
  · rw [stateOfIndex_eq]
    exact fun possible => possible
  · exact sample.eq_original

open Purelib.Algebra in
open Purelib.Data in
/-- Validate the exact quotient product and restore the complete canonical center.

Success retains equality to the original center using the supplied sample association. Failure records the unequal
product and expected numerator. -/
def checkCenter (edge : PreparedEdge curve differential) (data : Metadata)
    (associated : data = metadata edge) (index : { n : Nat // n = data.readingIndex })
    (sample : Sample edge) (value : Gaussian) :
    Except Invalidity { center : PreparedEdge.CenterState edge //
      center = PreparedEdge.CenterState.canonical edge } :=
  let product := value * sample.value
  if productEq : product = data.numerator then
    have quotient : value = edge.point 0 ^ differential.exponent / sample.value :=
      Gaussian.Field.mul_right_cancel_of_ne sample.nonzero
        (productEq.trans ((congrArg Metadata.numerator associated).trans
          (Field.ExplicitField.div_mul_cancel _ sample.nonzero).symm))
    .ok ⟨restoreCenter edge data associated index sample value quotient,
      restoreCenter_eq edge data associated index sample value quotient⟩
  else .error (.quotient product data.numerator productEq)

end Purelib.Riemann.Transport.PreparedCenterReplay
