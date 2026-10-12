module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.Squarefree
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Owner.Local.Track
import Purelib.RootIsolation.Power.Isolation
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Sheets.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Bounds.AccuracyRadius
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Line.Bezout
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Bezout
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Majorants
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Majorants
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Riemann.Branches.SquareRootSheets
public import Purelib.Riemann.RootContinuation.SquareRootContinuation
public import Purelib.RootIsolation.Newton.Extraction.Majorized.Build
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Newton.Build

import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.RootIsolation.Newton.Extraction.Separated.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.Data.Gaussian.Field
import Purelib.RootIsolation.Newton.Extraction.Majorized.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-!
# Finite same-owner square-root continuation chains

A root at each rational sample cannot be selected independently: the two
owners may be permuted by the isolator.  Here a sheet begins at one of the two
explicit power-polynomial owners and every subsequent owner is obtained by a
finite Rouché move from the preceding one.  The inductive chain is itself the
finite certificate that no pointwise re-indexing occurred.
-/

namespace Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
abbrev Gaussian := Basic.Canonical
open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Polynomial in
/-- Dense polynomials with rational Gaussian coordinates. -/
abbrev Polynomial := Dense.Basic.DensePolynomial Coordinate
/-- The original rational box type with retained coordinate bounds. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original winding-one root track indexed by its polynomial and ambient box. -/
abbrev WindingOneTrack := Purelib.RootIsolation.Track.Basic.WindingOneTrack

open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
set_option genInjectivity false in
/-- A nonzero radicand with its original ambient box and certified square-root track.

The track remains indexed by the quadratic polynomial of the retained parameter, preserving the selected root under
continuation and refinement. -/
structure Owner (parameter : Gaussian) where
  /-- The original radicand is nonzero. -/ parameterNonzero : parameter ≠ 0
  /-- The retained original ambient box of the square-root track. -/ ambient : Box
  /-- The winding-one track indexed by this exact radicand and ambient box. -/ track : WindingOneTrack
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
      SquareRootDegree.degreeTwo) ambient

constructive_injectivity Owner

namespace Owner

open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance.Owner

open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- The quadratic polynomial whose roots square to the original parameter. -/
abbrev rootPolynomial (parameter : Gaussian) :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
    SquareRootDegree.degreeTwo

open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Path
open Purelib.RootIsolation.Winding

open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Build a square-root owner by accelerating the original certified winding-one state.

The same quadratic parameter supplies squarefreeness and explicit axis elimination; the initial state's ambient box is
retained. -/
@[expose] def ofState {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    {ambient : Box}
    (initial : State.WindingOne.Basic.WindingOneState
      (rootPolynomial parameter) ambient) : Owner parameter where
  parameterNonzero := parameterNonzero
  ambient := ambient
  track := QuadraticLineClearance.Owner.accelerateTrack parameter
    (Track.Newton.Build.ofInitial
      (by
        rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
        decide)
      (Gaussian.Squarefree.squarefree parameterNonzero
        SquareRootDegree.degreeTwo)
      (QuadraticAxisElimination.quadraticAxisElimination parameter)
      initial)

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Clearance.Box in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Build a root owner from a proper winding-one box with four nonzero axis determinants.

The determinants give the exact boundary clearance witnesses, which are retained in the initial state passed to the
square-root track constructor. -/
@[expose] def ofBox {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (box : Box) (proper : box.Proper)
    (leftNonzero : QuadraticAxisElimination.verticalDeterminant parameter box.xLower ≠ 0)
    (rightNonzero : QuadraticAxisElimination.verticalDeterminant parameter box.xUpper ≠ 0)
    (bottomNonzero : QuadraticAxisElimination.horizontalDeterminant parameter box.yLower ≠ 0)
    (topNonzero : QuadraticAxisElimination.horizontalDeterminant parameter box.yUpper ≠ 0)
    (windingFour : Winding.Box.Basic.quadrupledBoxWinding (rootPolynomial parameter) box = 4) :
    Owner parameter := by
  let left := Line.Bezout.verticalOfCoprime
    (rootPolynomial parameter) box box.xLower
    (QuadraticAxisElimination.verticalCoprime parameter box.xLower leftNonzero)
  let right := Line.Bezout.verticalOfCoprime
    (rootPolynomial parameter) box box.xUpper
    (QuadraticAxisElimination.verticalCoprime parameter box.xUpper rightNonzero)
  let bottom := Line.Bezout.horizontalOfCoprime
    (rootPolynomial parameter) box box.yLower
    (QuadraticAxisElimination.horizontalCoprime parameter box.yLower bottomNonzero)
  let top := Line.Bezout.horizontalOfCoprime
    (rootPolynomial parameter) box box.yUpper
    (QuadraticAxisElimination.horizontalCoprime parameter box.yUpper topNonzero)
  let clearance := Boundary.Lines.boundaryOfLines left right bottom top
  exact ofState parameterNonzero
    { box := box
      refinesAmbient := Box.refines_refl box
      proper := proper
      clearance := clearance
      rawWindingFour := windingFour
      ambientLeftClearance := left
      ambientRightClearance := right
      ambientBottomClearance := bottom
      ambientTopClearance := top }

open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation in
/-- Read the root track's exact initial box, clearance and winding certificate as a local root owner.

The same track initial state supplies the box, properness, boundary clearance and raw winding fields; no new root or box
is selected. -/
@[expose] def localOwner {parameter : Gaussian} (owner : Owner parameter) :
    Owner.Local.Basic.LocalOwner
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        SquareRootDegree.degreeTwo) where
  box := owner.track.initial.box
  proper := owner.track.initial.proper
  clearance := owner.track.initial.clearance
  rawWindingFour := owner.track.initial.rawWindingFour

open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Polynomial.Power in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Select one of the two independently isolated square-root tracks of the original nonzero radicand.

The retained nonzero radicand and original Fin-two index identify the selected square-root track and its original
large-square ambient box. -/
@[expose] def independent {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) : Owner parameter where
  parameterNonzero := parameterNonzero
  ambient := Bounds.RootRadius.Box.largeSquareBox
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
      SquareRootDegree.degreeTwo)
  track := SquareRootSheets.track parameterNonzero sheet

open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- Continue the retained root owner to a nonzero target within the original boundary-clearance bound.

The returned track uses the certified common ambient box and preserves the selected root through the supplied
squared-displacement witness. -/
@[expose] def advance {source target : Gaussian} (owner : Owner source)
    (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound) : Owner target := by
  exact
    { parameterNonzero := targetNonzero
      ambient := SquareRootContinuation.commonAmbient
        owner.track.initial target
      track := SquareRootContinuation.continuedTrack
        targetNonzero owner.track.initial small }

section
open Purelib.Riemann.RootContinuation
/-- Restart the same root track at its indexed refined state.

The ambient owner and the original refinement operation, nesting, strictness and accuracy certificates are retained
unchanged. -/
@[expose] def refineAt {parameter : Gaussian} (owner : Owner parameter)
    (index : Nat) : Owner parameter where
  parameterNonzero := owner.parameterNonzero
  ambient := owner.ambient
  track :=
    { initial := CoherentRoot.state owner.track index
      refine := owner.track.refine
      nested := owner.track.nested
      strict := owner.track.strict
      accurate := owner.track.accurate }

/-- The restarted track's initial state is exactly the original indexed state. -/
@[simp] theorem refineAt_initial {parameter : Gaussian}
    (owner : Owner parameter) (index : Nat) :
    (refineAt owner index).track.initial =
      CoherentRoot.state owner.track index := rfl

/-- The restarted initial box refines the original initial box. -/
theorem refineAt_initial_refines {parameter : Gaussian}
    (owner : Owner parameter) (index : Nat) :
    (refineAt owner index).track.initial.box.Refines
      owner.track.initial.box :=
  CoherentRoot.state_refines_of_le owner.track
    (Nat.zero_le index)

end

section
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation
/-- Request a refinement index at least one meeting the positive squared-diameter target.

The original coherent approximation computes an index above the same stage floor one; its requested rational target and
strict positivity witness are retained. -/
@[expose] def preparationIndex {parameter : Gaussian} (owner : Owner parameter)
    (target : Fraction.Rational) (positive : 0 < target) : Nat :=
  (CoherentRoot.approximation owner.track).refineIndex
    1 target positive

/-- The retained preparation index is strictly positive.

The same refineIndex lower-bound certificate gives the original stage-floor inequality, which places the selected index
strictly above zero. -/
theorem preparationIndex_positive {parameter : Gaussian}
    (owner : Owner parameter)
    (target : Fraction.Rational) (positive : 0 < target) :
    0 < preparationIndex owner target positive := by
  exact (Nat.zero_lt_succ 0).trans_le
    ((CoherentRoot.approximation owner.track).refineIndex_ge
      1 target positive)

end

open Purelib.Data.Rat in
/-- Restart the original root track at its requested accurate preparation index.

The original preparation index selects the indexed state of the same track. Its ambient owner and refinement operation
remain unchanged. -/
@[expose] def prepare {parameter : Gaussian} (owner : Owner parameter)
    (target : Fraction.Rational) (positive : 0 < target) :
    Owner parameter :=
  refineAt owner (preparationIndex owner target positive)

open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- Compute the squarefree derivative-separation witness on the owner's original initial box.

The original nonzero quadratic and initial box supply the same squarefree Bezout derivative-separation calculation with
its retained finite cofactors. -/
@[expose] def quantitativePreparationSeparation {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0) :=
  Derivative.Separation.Bezout.ofSquarefree
    (Gaussian.Squarefree.squarefree parameterNonzero
      SquareRootDegree.degreeTwo) owner.track.initial.box

open Purelib.Polynomial.Dense.Gaussian in
/-- Compute exact Newton extraction majorants for the original quadratic and initial box.

The original quadratic coefficient table and same initial box supply the retained derivative, Lipschitz and Taylor
majorants. -/
@[expose] def quantitativePreparationMajorants {parameter : Gaussian}
    (owner : Owner parameter) :=
  Newton.Box.Majorants.exactExtractionMajorants (rootPolynomial parameter)
    owner.track.initial.box

section
open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Gaussian
/-- Predict a positive clearance bound from original separation, boundary clearance, majorants and target radius.

The same separation and majorants, original initial boundary clearance and accuracy radius determine this exact
predicted rational lower bound. -/
@[expose] def quantitativePreparedClearanceLower {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0)
    (target : Fraction.Rational) :
    Fraction.Rational :=
  Newton.Box.Budget.Majorants.predictedExtractionClearance
    (quantitativePreparationSeparation owner parameterNonzero)
    owner.track.initial.clearance
    (quantitativePreparationMajorants owner)
    (Bounds.AccuracyRadius.accuracyRadius target)

/-- The predicted clearance is strictly positive for a positive requested target. -/
theorem quantitativePreparedClearanceLower_positive {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0)
    (target : Fraction.Rational) (positive : 0 < target) :
    0 < quantitativePreparedClearanceLower owner parameterNonzero target := by
  exact Newton.Box.Budget.Majorants.predictedExtractionClearance_pos
    (quantitativePreparationSeparation owner parameterNonzero)
    owner.track.initial.clearance (quantitativePreparationMajorants owner)
    owner.track.initial.proper
    (Bounds.AccuracyRadius.accuracyRadius_pos positive)

end

open Purelib.Data.Rat in
open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation in
open Purelib.RootIsolation.Newton.Extraction in
/-- Run the certified majorized Newton extraction on the original initial state.

The exact quadratic supplies axis elimination and degree evidence; the retained separation and majorants control the
target accuracy radius. -/
@[expose] def quantitativePreparationOutput {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0)
    (target : Fraction.Rational) (positive : 0 < target) :=
  let p := rootPolynomial parameter
  let current := owner.track.initial.raw
  let separation := quantitativePreparationSeparation owner parameterNonzero
  let majorants := quantitativePreparationMajorants owner
  Majorized.Build.extractSeparatedMajorized
    (by
      rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
      exact SquareRootDegree.degreeTwo_atLeastTwo)
    current separation majorants
    (Power.Isolation.isolationInput parameterNonzero
      SquareRootDegree.degreeTwo
      SquareRootDegree.degreeTwo_atLeastTwo).elimination
    (Bounds.AccuracyRadius.accuracyRadius_pos positive)

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Clearance.Box in
open Purelib.RootIsolation in
/-- Read the extracted box as a winding-one state with its four boundary-clearance projections.

The extracted box is also the retained ambient box, and its properness and winding witness come from the same extraction
result. -/
@[expose] def quantitativePreparedInitial {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0)
    (target : Fraction.Rational) (positive : 0 < target) :
    State.WindingOne.Basic.WindingOneState
      (rootPolynomial parameter)
      (quantitativePreparationOutput owner parameterNonzero target
        positive).core.box := by
  let output := quantitativePreparationOutput owner parameterNonzero target
    positive
  let clearance := output.clearance
  let initial : State.WindingOne.Basic.WindingOneState
      (rootPolynomial parameter) output.core.box :=
    { box := output.core.box
      refinesAmbient := Box.refines_refl output.core.box
      proper := output.core.proper
      clearance := clearance
      rawWindingFour := output.core.rawWindingFour
      ambientLeftClearance := Boundary.Lines.leftOfBoundary clearance
      ambientRightClearance := Boundary.Lines.rightOfBoundary clearance
      ambientBottomClearance := Boundary.Lines.bottomOfBoundary clearance
      ambientTopClearance := Boundary.Lines.topOfBoundary clearance }
  exact initial

section
open Purelib.Data.Rat
/-- Build an accelerated root owner from the quantitative extraction's retained initial state.

The same majorized extraction output supplies the retained winding-one initial state, which is passed to the original
accelerated owner constructor. -/
@[expose] def quantitativePrepare {parameter : Gaussian} (owner : Owner parameter)
    (parameterNonzero : parameter ≠ 0)
    (target : Fraction.Rational) (positive : 0 < target) :
    Owner parameter := by
  let initial := quantitativePreparedInitial owner parameterNonzero target
    positive
  exact ofState parameterNonzero initial

/-- The quantitatively prepared initial box lies strictly inside the original initial box. -/
theorem quantitativePrepare_initial_strict {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0)
    (target : Fraction.Rational) (positive : 0 < target) :
    (quantitativePrepare owner parameterNonzero target positive).track.initial.box.StrictInterior
      owner.track.initial.box := by
  exact (quantitativePreparationOutput owner parameterNonzero target
    positive).core.strictCurrent

/-- The quantitatively prepared box has squared diagonal below the requested positive target. -/
theorem quantitativePrepare_diagonal_lt {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0)
    (target : Fraction.Rational) (positive : 0 < target) :
    (quantitativePrepare owner parameterNonzero target
      positive).track.initial.box.diagonalSq < target := by
  exact (quantitativePreparationOutput owner parameterNonzero target
    positive).core.diagonalSq_le.trans_lt
      (Bounds.AccuracyRadius.accuracyRadius_sq_lt positive)

/-- The predicted clearance lower bound is no larger than the prepared state's actual bound. -/
theorem quantitativePreparedClearanceLower_le {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0)
    (target : Fraction.Rational) (positive : 0 < target) :
    quantitativePreparedClearanceLower owner parameterNonzero target ≤
      (quantitativePrepare owner parameterNonzero target
        positive).track.initial.clearance.bound := by
  exact (quantitativePreparationOutput owner parameterNonzero target
    positive).predicted_clearance_le

end

attribute [irreducible] quantitativePrepare

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- The ordinary prepared initial box has squared diagonal below the requested positive target. -/
theorem prepare_diagonal_lt {parameter : Gaussian}
    (owner : Owner parameter)
    (target : Fraction.Rational) (positive : 0 < target) :
    (prepare owner target positive).track.initial.box.diagonalSq < target := by
  let approximation := CoherentRoot.approximation owner.track
  let index := preparationIndex owner target positive
  calc
    (prepare owner target positive).track.initial.box.diagonalSq <=
        Geometric.Basic.quarterRadius
          (CoherentRoot.scale owner.track) index :=
      CoherentRoot.state_diagonal_le owner.track index
    _ < target := approximation.refineIndex_accurate 1 target positive

open Purelib.Data.Rat in
/-- The ordinary prepared initial box refines the original initial box. -/
theorem prepare_initial_refines {parameter : Gaussian}
    (owner : Owner parameter)
    (target : Fraction.Rational) (positive : 0 < target) :
    (prepare owner target positive).track.initial.box.Refines
      owner.track.initial.box :=
  refineAt_initial_refines owner _

open Purelib.Riemann.RootContinuation in
/-- Produce the operational square-root certificate from this exact root track and nonzero parameter.

The same root track and supplied nonzero-parameter witness determine the original operational square-root certificate
and its retained coherent value. -/
@[expose] def certificate {parameter : Gaussian} (owner : Owner parameter)
    (parameterNonzero : parameter ≠ 0) :
    CertifiedSquareRoot.Certificate parameter :=
  CertifiedSquareRoot.certificate parameterNonzero owner.track

open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Every possible value of the owner's certified root process lies in its original initial box.

Possible values are later tailed samples, and the original track's nesting transports their anchor containment back to
that box. -/
theorem certificate_candidate_in_initial_box {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0)
    (state : (owner.certificate parameterNonzero).value.name.process.State)
    {candidate : Gaussian}
    (possible : (owner.certificate parameterNonzero).value.name.process.Possible
      state candidate) :
    owner.track.initial.box.Contains candidate := by
  change
    (CertifiedSquareRoot.approximation owner.track).Possible
      state.source candidate at possible
  rcases possible with ⟨later, order, rfl⟩
  simp only [CertifiedSquareRoot.approximation,
    SquareRootSheets.tail_sample,
    CoherentRoot.approximation_sample]
  exact (CoherentRoot.state_refines_of_le owner.track
    (Nat.zero_le _)).contains
      (CoherentRoot.state owner.track
        (max (CertifiedSquareRoot.baseIndex owner.track)
          later)).box.contains_anchor

open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- Continuing to a nearby nonzero parameter retains an initial box refining the source initial box. -/
theorem advance_initial_box_refines {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound) :
    (advance owner targetNonzero small).track.initial.box.Refines
      owner.track.initial.box :=
  SquareRootContinuation.continuedTrack_initial_refines_source
    targetNonzero owner.track.initial small

open Purelib.Data.Gaussian in
/-- The continued owner's initial boundary-clearance bound is strictly positive. -/
theorem advance_clearance_positive {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound) :
    0 < (advance owner targetNonzero small).track.initial.clearance.bound :=
  (advance owner targetNonzero small).track.initial.clearance.positive

open Purelib.Riemann.Branches in
/-- The independently selected owner's certified value is exactly the original selected sheet value. -/
@[simp] theorem independent_root_eq {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) :
    (certificate (independent parameterNonzero sheet) parameterNonzero).value =
      (SquareRootSheets.sheet parameterNonzero sheet).value :=
  rfl

end Owner

set_option genInjectivity false in
/-- A radicand paired dependently with its certified square-root owner.

The original Gaussian parameter indexes the exact retained square-root track and its ambient box; the dependent owner is
neither copied nor reselected. -/
structure PackedOwner where
  /-- The retained Gaussian radicand. -/ parameter : Gaussian
  /-- The certified square-root owner indexed by the retained radicand. -/ owner : Owner parameter

constructive_injectivity PackedOwner

namespace PackedOwner

/-- Pair the original nonzero radicand with its independently selected sheet owner.

The retained nonzero radicand and original Fin-two index identify the selected square-root track and its original
large-square ambient box. -/
@[expose] def independent {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) : PackedOwner :=
  ⟨parameter, Owner.independent parameterNonzero sheet⟩

open Purelib.Data.Gaussian in
/-- Pair the nonzero target with the exact continued owner produced from the retained source owner.

The supplied squared-displacement bound permits the retained source owner
to advance to this target. The result contains that exact advanced owner. -/
@[expose] def advance (current : PackedOwner) (target : Gaussian)
    (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq
      (current.parameter - target) <
        current.owner.track.initial.clearance.bound) : PackedOwner :=
  ⟨target, current.owner.advance targetNonzero small⟩

end PackedOwner

open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- A finite continuation chain retaining the exact owner before and after each clearance-bounded step.

Each target is nonzero, and the tail starts from the actual advanced owner produced using that step's displacement
witness. -/
inductive Chain : PackedOwner → Type
  /-- The empty continuation chain retaining its current owner as endpoint. -/ | nil (owner : PackedOwner) : Chain owner
  /-- A clearance-bounded continuation step followed by a chain at the exact advanced owner. -/ | step (owner :
    PackedOwner) (target : Gaussian)
      (targetNonzero : target ≠ 0)
      (small : Data.Gaussian.Norm.Basic.normSq
        (owner.parameter - target) <
          owner.owner.track.initial.clearance.bound)
      (remaining : Chain
        (owner.advance target targetNonzero small)) :
      Chain owner

constructive_injectivity Chain

namespace Chain

/-- Count the number of continuation steps in the retained chain.

The empty chain has no moves. Each original step increments the count of its retained continuation tail without
recomputing any root owner. -/
@[expose] def length {initial : PackedOwner} : Chain initial → Nat
  | .nil _ => 0
  | .step _ _ _ _ remaining => remaining.length + 1

/-- Read the exact terminal packed owner of the retained continuation chain.

The exact terminal packed owner is read through the original retained continuation tail; the empty chain returns its
retained owner itself. -/
@[expose] def endpoint {initial : PackedOwner} : Chain initial → PackedOwner
  | .nil owner => owner
  | .step _ _ _ _ remaining => remaining.endpoint

/-- List every visited radicand, including the initial and terminal parameters.

Every original step contributes its source radicand in order; the empty tail contributes the terminal radicand once. -/
@[expose] def parameters {initial : PackedOwner} : Chain initial → List Gaussian
  | .nil owner => [owner.parameter]
  | .step owner _ _ _ remaining =>
      owner.parameter :: remaining.parameters

/-- The visited parameter list has one more entry than the number of continuation steps.

Each original step prepends its retained source radicand and increments the
same tail's step count. The empty chain retains its endpoint once. -/
@[simp] theorem parameters_length {initial : PackedOwner}
    (chain : Chain initial) :
    chain.parameters.length = chain.length + 1 := by
  induction chain with
  | nil => rfl
  | step owner target targetNonzero small remaining inductionHypothesis =>
      change remaining.parameters.length + 1 = (remaining.length + 1) + 1
      exact congrArg (fun count : Nat => count + 1) inductionHypothesis

/-- A chain starting from a nonzero parameter ends at a nonzero parameter. -/
theorem endpointNonzero {initial : PackedOwner} (chain : Chain initial)
    (initialNonzero : initial.parameter ≠ 0) :
    chain.endpoint.parameter ≠ 0 :=
  match chain with
  | .nil _ => initialNonzero
  | .step _ _ targetNonzero _ remaining =>
      remaining.endpointNonzero targetNonzero

open Purelib.Data.Gaussian
/-- Build one certified continuation step followed by the empty chain at its actual advanced owner.

The supplied nonzero target and squared-displacement witness index the exact advanced owner. The empty tail retains that
same computed owner. -/
@[expose] def single (owner : PackedOwner) (target : Gaussian)
    (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq
      (owner.parameter - target) <
        owner.owner.track.initial.clearance.bound) : Chain owner :=
  .step owner target targetNonzero small (.nil _)

/-- A single-step continuation chain has length one. -/
@[simp] theorem length_single (owner : PackedOwner) (target : Gaussian)
    (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq
      (owner.parameter - target) <
        owner.owner.track.initial.clearance.bound) :
    (single owner target targetNonzero small).length = 1 := rfl

/-- The endpoint of a single-step chain is its exact advanced owner. -/
@[simp] theorem endpoint_single (owner : PackedOwner) (target : Gaussian)
    (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq
      (owner.parameter - target) <
        owner.owner.track.initial.clearance.bound) :
    (single owner target targetNonzero small).endpoint =
      owner.advance target targetNonzero small := rfl

end Chain

set_option genInjectivity false in
/-- A finite continuation chain retaining its original choice of independently isolated sheet.

The chain starts at the owner determined by the same nonzero source and retained sheet index. -/
structure SeededChain (source : Gaussian) (sourceNonzero : source ≠ 0) where
  /-- The retained original choice of one of the two independently isolated sheets. -/ sheet : Fin 2
  /-- The finite continuation chain starting from this exact selected source owner. -/ continuation : Chain
    (PackedOwner.independent sourceNonzero sheet)

constructive_injectivity SeededChain

namespace SeededChain

/-- Build an empty continuation chain at the selected independently isolated source sheet.

The original nonzero source and Fin-two index choose the exact starting owner; the retained continuation is the empty
chain at that owner. -/
@[expose] def initial (source : Gaussian) (sourceNonzero : source ≠ 0)
    (sheet : Fin 2) : SeededChain source sourceNonzero where
  sheet := sheet
  continuation := .nil (PackedOwner.independent sourceNonzero sheet)

/-- Read the exact terminal owner of the seeded continuation chain.

The exact terminal packed owner is read through the original retained continuation tail; the empty chain returns its
retained owner itself. -/
@[expose] def endpoint {source : Gaussian} {sourceNonzero : source ≠ 0}
    (chain : SeededChain source sourceNonzero) : PackedOwner :=
  chain.continuation.endpoint

/-- An empty seeded chain ends at its original source parameter. -/
@[simp] theorem initial_endpoint_parameter (source : Gaussian)
    (sourceNonzero : source ≠ 0) (sheet : Fin 2) :
    (initial source sourceNonzero sheet).endpoint.parameter = source := rfl

open Purelib.Riemann.RootContinuation in
/-- Certify the exact terminal root of the retained seeded continuation chain.

The retained terminal owner supplies the certificate, and the original finite continuation supplies its terminal nonzero
witness. -/
@[expose] def rootCertificate {source : Gaussian} {sourceNonzero : source ≠ 0}
    (chain : SeededChain source sourceNonzero) :
    CertifiedSquareRoot.Certificate chain.endpoint.parameter :=
  chain.endpoint.owner.certificate
    (chain.continuation.endpointNonzero sourceNonzero)

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Polynomial in
/-- Read the terminal root as an algebraic sheet value over the specified curve point.

The supplied endpoint identity identifies the terminal radicand with the curve polynomial value, while the original
sheet index and apartness certificate are retained. -/
@[expose] def algebraicSheetValue {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (point source : Gaussian) (sourceNonzero : source ≠ 0)
    (chain : SeededChain source sourceNonzero)
    (endpoint_eq : chain.endpoint.parameter = curve.polynomial.eval point) :
    Curves.Hyperelliptic.Sheets.Basic.AlgebraicSheetValue curve point := by
  let root := chain.rootCertificate
  have rootSquare : Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.mul root.value root.value).name
      (Name.Basic.Named.exact
        (curve.polynomial.eval point)) := by
    rw [← endpoint_eq]
    exact root.square
  exact
    { value := root.value
      apart := root.apart
      sheet := chain.sheet
      curveEquation :=
        Equivalence.NamedEquivalent.trans rootSquare
          (Equivalence.NamedEquivalent.symm
            (Approximation.Gaussian.Evaluation.Horner.polynomialEval_exact
              curve.polynomial point)) }

end SeededChain

end Purelib.Riemann.Topology.SquareRootContinuationChain

end
