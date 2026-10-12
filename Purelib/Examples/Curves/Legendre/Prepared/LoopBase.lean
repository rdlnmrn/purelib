module
import Purelib.Data.Fin

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Fin.Two
import Purelib.Data.Fin.Cases
import Purelib.Polynomial.Power.Gaussian
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Construction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Examples.Curves.Legendre.LoopBaseBranches
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Paths.PreparedClearPathModels
public import Purelib.Riemann.Paths.PreparedClearPathModels.Execution
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.Deriving.Repr
public import Purelib.Data.Rat.Fraction.Construction.Bezout

section
public section

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

namespace Purelib.Examples.Curves.Legendre.Prepared.LoopBase

open Purelib.Data.Gaussian
open Purelib.Data.Fin
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Basis (CertifiedPeriodProgram)
open Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath

open Purelib

open Purelib.Data.Rat.Fraction.Construction

open Purelib.Examples.Curves.Legendre

open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.PreparedCycleModels (RootClosedPeriodBank)

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Examples

open Purelib.Geometry

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

/-- The reduced rational `17/8` with its explicit Bezout reduction witness. -/
@[expose] def q17_8 : Fraction.Rational :=
  Bezout.ofCoefficients 17 8 (by decide) 1 (-2) (by decide)

/-- The reduced rational `-137/512` with its explicit Bezout reduction witness. -/
@[expose] def qNeg137_512 : Fraction.Rational :=
  Bezout.ofCoefficients (-137) 512 (by decide) (-71) 19 (by decide)

/-- The reduced rational `169/128` with its explicit Bezout reduction witness. -/
@[expose] def q169_128 : Fraction.Rational :=
  Bezout.ofCoefficients 169 128 (by decide) 25 (-33) (by decide)

/-- The reduced rational `-5349/4096` with its explicit Bezout reduction witness. -/
@[expose] def qNeg5349_4096 : Fraction.Rational :=
  Bezout.ofCoefficients (-5349) 4096 (by decide) (-1811) 2365 (by decide)

/-- The reduced rational `241/512` with its explicit Bezout reduction witness. -/
@[expose] def q241_512 : Fraction.Rational :=
  Bezout.ofCoefficients 241 512 (by decide) 17 (-8) (by decide)

/-- The displayed base branch data has three sites. -/
theorem baseBranchData_siteCount : (LoopBaseBranches.baseBranchData ()).siteCount = 3 := rfl

/-- Transport a displayed three-element branch index to the original branch-data index type. -/
@[expose] def branchIndex (index : Fin 3) :
    Hyperelliptic.Branches.BranchIsolation.Data.Index (LoopBaseBranches.baseBranchData ()) :=
  Fin.cast baseBranchData_siteCount.symm index

/-! ## Explicit quadratic sheet owners at the branch-box anchors -/

/-- Lower-left anchors of the three large period boxes. -/
@[expose] def squareRootEndpointPoint (index : Fin 3) : Gaussian.Basic.Canonical :=
  Nat.casesOn (motive := fun _ => Gaussian.Basic.Canonical) index.val
    (Gaussian.Basic.ExplicitLegendrePreparedPeriods.point (-(1 / 2)) (-(1 / 2)))
    (fun previous => Nat.casesOn (motive := fun _ => Gaussian.Basic.Canonical) previous
      (Gaussian.Basic.ExplicitLegendrePreparedPeriods.point (1 / 8) (3 / 2))
      (fun _ => Gaussian.Basic.ExplicitLegendrePreparedPeriods.point (15 / 16) (-(1 / 2))))

/-- The exact Legendre radicands at the three displayed anchors.  Keeping
these as a three-entry table makes the subsequent finite determinant and
winding checks reduce directly, without unfolding polynomial normalization
inside every decision procedure. -/
@[expose] def squareRootParameter (index : Fin 3) : Gaussian.Basic.Canonical :=
  Nat.casesOn (motive := fun _ => Gaussian.Basic.Canonical) index.val
    (Gaussian.Basic.ExplicitLegendrePreparedPeriods.point q17_8 (-2))
    (fun previous => Nat.casesOn (motive := fun _ => Gaussian.Basic.Canonical) previous
      (Gaussian.Basic.ExplicitLegendrePreparedPeriods.point qNeg137_512
        q169_128)
      (fun _ => Gaussian.Basic.ExplicitLegendrePreparedPeriods.point qNeg5349_4096
        q241_512))

/-- The Legendre polynomial at each displayed anchor equals its retained radicand table entry. -/
theorem basePolynomial_eval_squareRootEndpointPoint (index : Fin 3) :
    LoopBaseBranches.baseCurve.polynomial.eval
      (squareRootEndpointPoint index) =
      squareRootParameter index := by
  rcases Cases.three index with h | h | h <;> subst index <;>
    rw [LoopBaseBranches.baseCurve_polynomial,
      Legendre.Paths.polynomial_eval] <;>
    apply Gaussian.Basic.ext <;>
    apply Fraction.Rational.ext <;> rfl

/-- Resultant-optimized rational rectangles around the two square roots of
each endpoint radicand.  The second sheet is the point reflection of the
first.  These deliberately asymmetric boxes keep every side far from both
quadratic roots and therefore avoid repeated moving-owner resets. -/
@[expose] def squareRootOwnerBox (index : Fin 3) (sheet : Fin 2) : Rational.Box :=
  Nat.casesOn (motive := fun _ => Rational.Box) index.val
    (Nat.casesOn (motive := fun _ => Rational.Box) sheet.val
        ({ xLower := 1 / 8, xUpper := 2, yLower := -(2 / 3), yUpper := 3 / 2,
           x_valid := by decide +revert,
           y_valid := by decide +revert })
        (fun _ => { xLower := -2, xUpper := -(1 / 8), yLower := -3 / 2, yUpper := 2 / 3,
                    x_valid := by decide +revert,
                    y_valid := by decide +revert }))
    (fun previous => Nat.casesOn (motive := fun _ => Rational.Box) previous
      (Nat.casesOn (motive := fun _ => Rational.Box) sheet.val
        ({ xLower := 1 / 4, xUpper := 5 / 4, yLower := 1 / 4, yUpper := 3 / 2,
           x_valid := by decide +revert,
           y_valid := by decide +revert })
        (fun _ => { xLower := -5 / 4, xUpper := -(1 / 4), yLower := -3 / 2, yUpper := -(1 / 4),
                    x_valid := by decide +revert,
                    y_valid := by decide +revert }))
      (fun _ => Nat.casesOn (motive := fun _ => Rational.Box) sheet.val
        ({ xLower := 1 / 16, xUpper := 3 / 4, yLower := 1 / 2, yUpper := 3 / 2,
           x_valid := by decide +revert,
           y_valid := by decide +revert })
        (fun _ => { xLower := -3 / 4, xUpper := -(1 / 16), yLower := -3 / 2, yUpper := -(1 / 2),
                    x_valid := by decide +revert,
                    y_valid := by decide +revert })))

/-- Every displayed sheet-owner rectangle has strictly ordered coordinate bounds. -/
theorem squareRootOwnerBox_proper (index : Fin 3) (sheet : Fin 2) :
    (squareRootOwnerBox index sheet).Proper := by
  rcases Cases.three index with h | h | h <;> subst index <;>
    rcases Data.Fin.Two.finTwo_cases sheet with h | h <;> subst sheet <;>
    constructor <;> decide

/-- The quadratic polynomial whose roots are square roots of the retained anchor radicand. -/
@[expose] def squareRootPolynomial (index : Fin 3) :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial (squareRootParameter index)
    RootContinuation.SquareRootDegree.degreeTwo

/-- Every displayed anchor radicand is nonzero. -/
theorem squareRootParameter_nonzero :
    ∀ index : Fin 3, squareRootParameter index ≠ 0 := by
  intro index
  rcases Cases.three index with h | h | h <;> subst index <;> decide

/-- The vertical elimination determinant is nonzero on the left side of every displayed sheet-owner box. -/
theorem squareRootOwner_leftNonzero : ∀ index : Fin 3, ∀ sheet : Fin 2,
    SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      (squareRootParameter index)
        (squareRootOwnerBox index sheet).xLower ≠
        0 := by
  intro index sheet
  rcases Cases.three index with h | h | h <;> subst index <;>
    rcases Data.Fin.Two.finTwo_cases sheet with h | h <;> subst sheet <;> decide

/-- The vertical elimination determinant is nonzero on the right side of every displayed sheet-owner box. -/
theorem squareRootOwner_rightNonzero : ∀ index : Fin 3, ∀ sheet : Fin 2,
    SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      (squareRootParameter index)
        (squareRootOwnerBox index sheet).xUpper ≠
        0 := by
  intro index sheet
  rcases Cases.three index with h | h | h <;> subst index <;>
    rcases Data.Fin.Two.finTwo_cases sheet with h | h <;> subst sheet <;> decide

/-- The horizontal elimination determinant is nonzero on the bottom side of every displayed sheet-owner box. -/
theorem squareRootOwner_bottomNonzero :
    ∀ index : Fin 3, ∀ sheet : Fin 2,
    SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      (squareRootParameter index)
        (squareRootOwnerBox index sheet).yLower ≠
        0 := by
  intro index sheet
  rcases Cases.three index with h | h | h <;> subst index <;>
    rcases Data.Fin.Two.finTwo_cases sheet with h | h <;> subst sheet <;> decide

/-- The horizontal elimination determinant is nonzero on the top side of every displayed sheet-owner box. -/
theorem squareRootOwner_topNonzero : ∀ index : Fin 3, ∀ sheet : Fin 2,
    SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      (squareRootParameter index)
        (squareRootOwnerBox index sheet).yUpper ≠
        0 := by
  intro index sheet
  rcases Cases.three index with h | h | h <;> subst index <;>
    rcases Data.Fin.Two.finTwo_cases sheet with h | h <;> subst sheet <;> decide

/-- The quadratic has quadrupled boundary winding four on each displayed sheet-owner box. -/
theorem squareRootOwner_windingFour :
    ∀ index : Fin 3, ∀ sheet : Fin 2,
    Winding.Box.Basic.quadrupledBoxWinding (squareRootPolynomial index)
      (squareRootOwnerBox index sheet) = 4 := by
  intro index sheet
  rcases Cases.three index with h | h | h <;> subst index <;>
    rcases Data.Fin.Two.finTwo_cases sheet with h | h <;> subst sheet <;> decide

/-- A complete local owner for either square-root sheet at each displayed
branch anchor, without invoking the generic all-root isolator. -/
@[expose] def squareRootOwner (index : Fin 3) (sheet : Fin 2) :
    Topology.SquareRootContinuationChain.Owner
      (squareRootParameter index) :=
  SquareRoot.Clearance.ExactQuadraticOwnerClearance.directOwnerOfBox
    (squareRootParameter index)
      (squareRootParameter_nonzero index)
    (squareRootOwnerBox index sheet)
    (squareRootOwnerBox_proper index sheet)
    (squareRootOwner_leftNonzero index sheet)
    (squareRootOwner_rightNonzero index sheet)
    (squareRootOwner_bottomNonzero index sheet)
    (squareRootOwner_topNonzero index sheet)
    (squareRootOwner_windingFour index sheet)

/-- The original branch track at refinement zero has the displayed square-root endpoint anchor. -/
theorem refinedTrackAnchor_eq_squareRootEndpointPoint (index : Fin 3) :
    Hyperelliptic.Branches.Cuts.refinedTrackAnchor (LoopBaseBranches.baseBranchData ())
        LoopBaseBranches.baseCurve_degree_gt_one (branchIndex index) 0
          =
      squareRootEndpointPoint index := by
  refine Purelib.Data.Fin.cases_induction (by rfl) (fun next => ?_) index
  refine Purelib.Data.Fin.cases_induction (by rfl) (fun final => ?_) next
  refine Purelib.Data.Fin.cases_induction (by rfl) (fun empty => ?_) final
  exact Fin.elim0 empty

/-- The original base-branch state selected by its three-element index. -/
@[expose] def branchState (index : Fin 3) :=
  LoopBaseBranches.baseBranchStateAt index

/-- The selected branch-state anchor equals the displayed square-root endpoint. -/
theorem branchState_anchor_eq_squareRootEndpointPoint (index : Fin 3) :
    (branchState index).box.anchor =
      squareRootEndpointPoint index := by
  refine Purelib.Data.Fin.cases_induction (by rfl) (fun next => ?_) index
  refine Purelib.Data.Fin.cases_induction (by rfl) (fun final => ?_) next
  refine Purelib.Data.Fin.cases_induction (by rfl) (fun empty => ?_) final
  exact Fin.elim0 empty

/-- The retained square-root owner transported to the polynomial value at its original branch-state anchor. -/
@[expose] def branchSquareRootOwner (index : Fin 3) (sheet : Fin 2) :
    Topology.SquareRootContinuationChain.Owner
      (LoopBaseBranches.baseCurve.polynomial.eval
        (branchState index).box.anchor) := by
  rw [branchState_anchor_eq_squareRootEndpointPoint]
  rw [basePolynomial_eval_squareRootEndpointPoint]
  exact squareRootOwner index sheet

/-! ## Explicitly bounded prepared path banks -/

/-- Outer refinement tightens the polynomial majorants on the canonical
connectors before the local continuation checker runs. -/
@[expose] def connectorOuterDepth : Nat := 4

/-- The uniform outer boundary refinement depth, two. -/
@[expose] def boundaryOuterDepth : Nat := 2

/-- Measured outer depths for the two raw A-connector segments.  The
horizontal leg succeeds two levels earlier than the vertical leg. -/
@[expose] def aConnectorOuterDepths : List Nat := [2, 4]

/-- The B connector is horizontal.  Its second raw segment is stationary, so
subdividing that segment sixteen ways only creates duplicate zero-length cells.
Retaining one stationary segment preserves the canonical raw connector while
removing fifteen redundant outer cells from each direction. -/
@[expose] def bConnectorOuterDepths : List Nat := [4, 0]

/-- Measured outer depths for the four sides of the right A boundary. -/
@[expose] def rightBoundaryOuterDepths : List Nat := [2, 2, 2, 3]

/-- The left boundary retains its common successful outer depth, expressed
through the same scheduled interface as the other A pieces. -/
@[expose] def leftBoundaryOuterDepths : List Nat := [2, 2, 2, 2]

/-- Measured local depths are retained per path piece.  The A connector uses
depth five, the scheduled right boundary uses four, the left winding boundary
needs seven, and the two B directions share their least common successful
depth three. -/
@[expose] def connectorInnerDepth : Nat := 5

/-- The local refinement depth of the scheduled right boundary, four. -/
@[expose] def rightBoundaryInnerDepth : Nat := 4

/-- The local refinement depth of the left boundary, seven. -/
@[expose] def leftBoundaryInnerDepth : Nat := 7

/-- The common local refinement depth of the two B connector directions, three. -/
@[expose] def bConnectorInnerDepth : Nat := 3

/-- Every displayed owner rectangle admits the measured diameter-`11`
reconditioning request used by all six successful path banks.  Retaining the
smallest common tested value materially tightens every downstream period
allowance without changing the certified meshes. -/
@[expose] def workingRootDiameter : Fraction.Rational := 11

/-- The retained working root-diameter request is positive. -/
theorem workingRootDiameter_positive : 0 < workingRootDiameter :=
  Fraction.Cast.Order.natCast_pos_direct (by decide)

/-- A dyadic continuation bank for the original path and starting owner at the specified depth.

The bank retains the common positive root-diameter request and the path-indexed continuation certificates. -/
abbrev WorkingBank (depth : Nat) {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
    (path : Polynomial.Geometry.ClearPath LoopBaseBranches.baseCurve.polynomial ambient
      start finish)
    (owner : Topology.SquareRootContinuationChain.Owner
      (LoopBaseBranches.baseCurve.polynomial.eval start)) :=
  DyadicBank
    depth workingRootDiameter
      workingRootDiameter_positive path
      owner

/-- A retained direct execution of the original path, owner and working diameter request.

The report retains its completed prefix and typed stopping reason, so a finite
unfinished attempt can be inspected or resumed without rebuilding that prefix. -/
abbrev WorkingAttempt (depth : Nat) {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
    (path : Polynomial.Geometry.ClearPath LoopBaseBranches.baseCurve.polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Topology.SquareRootContinuationChain.Owner
      (LoopBaseBranches.baseCurve.polynomial.eval start)) :=
  DyadicBank.Execution .direct depth
    workingRootDiameter workingRootDiameter_positive path within owner

/-- The horizontal-then-vertical clear connector between two retained branch anchors.

Its coordinate bounds and clearances come from the original endpoint branch states. -/
@[expose] def rawConnector (left right : Fin 3) :
    Polynomial.Geometry.ClearPath LoopBaseBranches.baseCurve.polynomial
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox LoopBaseBranches.baseCurve.polynomial)
      (branchState left).box.anchor (branchState
        right).box.anchor := by
  let leftState := branchState left
  let rightState := branchState right
  exact Polynomial.Geometry.ClearPath.cons
    (.horizontal leftState.box.xLower rightState.box.xLower
      leftState.box.yLower
      leftState.refinesAmbient.1
      (leftState.box.x_valid.trans leftState.refinesAmbient.2.1)
      rightState.refinesAmbient.1
      (rightState.box.x_valid.trans rightState.refinesAmbient.2.1)
      leftState.ambientBottomClearance)
    (.cons
      (.vertical rightState.box.xLower leftState.box.yLower
        rightState.box.yLower
        leftState.refinesAmbient.2.2.1
        (leftState.box.y_valid.trans leftState.refinesAmbient.2.2.2)
        rightState.refinesAmbient.2.2.1
        (rightState.box.y_valid.trans rightState.refinesAmbient.2.2.2)
        rightState.ambientLeftClearance)
      (.nil rightState.box.anchor))

/-- The raw connector lies within its original ambient box. -/
theorem rawConnector_withinAmbient (left right : Fin 3) :
    (rawConnector left right).WithinAmbient :=
  .cons
    ⟨(branchState left).refinesAmbient.2.2.1,
      (branchState left).box.y_valid.trans
        (branchState left).refinesAmbient.2.2.2⟩
    (.cons
      ⟨(branchState right).refinesAmbient.1,
        (branchState right).box.x_valid.trans
          (branchState right).refinesAmbient.2.1⟩
      (.nil _))

/-- The uniform depth-four dyadic refinement of the original two-anchor connector. -/
@[expose] def workingConnector (left right : Fin 3) :=
  Paths.PreparedClearPathModels.dyadicRefinePath
    (rawConnector left right)
      (rawConnector_withinAmbient left right)
      connectorOuterDepth

/-- The uniformly refined connector lies within its original ambient box. -/
theorem workingConnector_withinAmbient (left right : Fin 3) :
    (workingConnector left right).WithinAmbient :=
  Paths.PreparedClearPathModels.dyadicRefinePath_withinAmbient
    (rawConnector left right)
      (rawConnector_withinAmbient left right)
      connectorOuterDepth

/-- The reversal of the uniformly refined connector. -/
@[expose] def workingBackwardConnector (left right : Fin 3) :=
  Hyperelliptic.Branches.BranchCutLifts.ClearPath.reverse (workingConnector left
    right)

/-- The reversed uniform connector lies within its original ambient box. -/
theorem workingBackwardConnector_withinAmbient (left right : Fin 3) :
    (workingBackwardConnector left right).WithinAmbient :=
  Hyperelliptic.Branches.BranchCutLifts.ClearPath.reverse_withinAmbient
    (workingConnector left right)
      (workingConnector_withinAmbient left right)

/-- Scheduled refinement of the canonical B connector.  This is geometrically
the same refinement used by the former uniform-depth construction, except that
its stationary second segment is retained only once. -/
@[expose] def workingBConnector :=
  Paths.PreparedClearPathModels.dyadicRefinePathScheduled
    (rawConnector 0 2) (rawConnector_withinAmbient 0
      2)
      bConnectorOuterDepths

/-- The scheduled B connector lies within its original ambient box. -/
theorem workingBConnector_withinAmbient : workingBConnector.WithinAmbient :=
  Paths.PreparedClearPathModels.dyadicRefinePathScheduled_withinAmbient
    (rawConnector 0 2) (rawConnector_withinAmbient 0
      2)
      bConnectorOuterDepths

/-- The reversal of the scheduled B connector, retaining its single stationary segment. -/
@[expose] def workingBBackwardConnector :=
  Hyperelliptic.Branches.BranchCutLifts.ClearPath.reverse workingBConnector

/-- The reversed scheduled B connector lies within its original ambient box. -/
theorem workingBBackwardConnector_withinAmbient :
    workingBBackwardConnector.WithinAmbient :=
  Hyperelliptic.Branches.BranchCutLifts.ClearPath.reverse_withinAmbient
    workingBConnector
      workingBConnector_withinAmbient

/-- The A connector refined with the original horizontal and vertical depth schedule `[2, 4]`. -/
@[expose] def workingAConnector :=
  Paths.PreparedClearPathModels.dyadicRefinePathScheduled
    (rawConnector 0 1) (rawConnector_withinAmbient 0
      1)
      aConnectorOuterDepths

/-- The scheduled A connector lies within its original ambient box. -/
theorem workingAConnector_withinAmbient : workingAConnector.WithinAmbient :=
  Paths.PreparedClearPathModels.dyadicRefinePathScheduled_withinAmbient
    (rawConnector 0 1) (rawConnector_withinAmbient 0
      1)
      aConnectorOuterDepths

/-- The reversal of the scheduled A connector. -/
@[expose] def workingABackwardConnector :=
  Hyperelliptic.Branches.BranchCutLifts.ClearPath.reverse workingAConnector

/-- The reversed scheduled A connector lies within its original ambient box. -/
theorem workingABackwardConnector_withinAmbient :
    workingABackwardConnector.WithinAmbient :=
  Hyperelliptic.Branches.BranchCutLifts.ClearPath.reverse_withinAmbient
    workingAConnector
      workingAConnector_withinAmbient

/-- The positively oriented boundary path of the original branch-state box. -/
@[expose] def rawBoundary (index : Fin 3) :=
  Hyperelliptic.Branches.BranchCutLifts.ownerBoundaryPath (branchState index)

/-- The original branch boundary lies within its original ambient box. -/
theorem rawBoundary_withinAmbient (index : Fin 3) :
    (rawBoundary index).WithinAmbient :=
  Hyperelliptic.Branches.BranchCutLifts.ownerBoundaryPath_withinAmbient
    (branchState index)

/-- The uniform depth-two dyadic refinement of the original branch boundary. -/
@[expose] def workingBoundary (index : Fin 3) :=
  Paths.PreparedClearPathModels.dyadicRefinePath
    (rawBoundary index) (rawBoundary_withinAmbient
      index) boundaryOuterDepth

/-- The uniformly refined branch boundary lies within its original ambient box. -/
theorem workingBoundary_withinAmbient (index : Fin 3) :
    (workingBoundary index).WithinAmbient :=
  Paths.PreparedClearPathModels.dyadicRefinePath_withinAmbient
    (rawBoundary index) (rawBoundary_withinAmbient
      index) boundaryOuterDepth

/-- The right A boundary refined with the retained side schedule `[2, 2, 2, 3]`. -/
@[expose] def workingRightBoundary :=
  Paths.PreparedClearPathModels.dyadicRefinePathScheduled
    (rawBoundary 1) (rawBoundary_withinAmbient 1)
      rightBoundaryOuterDepths

/-- The scheduled right boundary lies within its original ambient box. -/
theorem workingRightBoundary_withinAmbient :
    workingRightBoundary.WithinAmbient :=
  Paths.PreparedClearPathModels.dyadicRefinePathScheduled_withinAmbient
    (rawBoundary 1) (rawBoundary_withinAmbient 1)
      rightBoundaryOuterDepths

/-- The left A boundary refined with the retained side schedule `[2, 2, 2, 2]`. -/
@[expose] def workingLeftBoundary :=
  Paths.PreparedClearPathModels.dyadicRefinePathScheduled
    (rawBoundary 0) (rawBoundary_withinAmbient 0)
      leftBoundaryOuterDepths

/-- The scheduled left boundary lies within its original ambient box. -/
theorem workingLeftBoundary_withinAmbient :
    workingLeftBoundary.WithinAmbient :=
  Paths.PreparedClearPathModels.dyadicRefinePathScheduled_withinAmbient
    (rawBoundary 0) (rawBoundary_withinAmbient 0)
      leftBoundaryOuterDepths

/-- The scheduled left boundary is exactly its uniform depth-two refinement. -/
theorem workingLeftBoundary_eq_uniform :
    workingLeftBoundary = workingBoundary 0 := by
  rfl

/-- Execute the forward A connector at the requested depth and retain its finite result.

The original path, starting sheet owner and diameter request index the report.
An inconclusive result retains its successful prefix and stopping evidence. -/
opaque aForwardAttempt (depth : Nat) :
    WorkingAttempt depth workingAConnector workingAConnector_withinAmbient (branchSquareRootOwner 0 0) :=
  DyadicBank.execute
    workingAConnector workingAConnector_withinAmbient (branchSquareRootOwner 0 0) depth
    workingRootDiameter workingRootDiameter_positive

/-- Execute the right A boundary at the requested depth and retain its finite result.

The original path, starting sheet owner and diameter request index the report.
An inconclusive result retains its successful prefix and stopping evidence. -/
opaque aRightBoundaryAttempt (depth : Nat) :
    WorkingAttempt depth workingRightBoundary workingRightBoundary_withinAmbient (branchSquareRootOwner 1 0) :=
  DyadicBank.execute
    workingRightBoundary workingRightBoundary_withinAmbient (branchSquareRootOwner 1 0) depth
    workingRootDiameter workingRootDiameter_positive

/-- Execute the backward A connector at the requested depth and retain its finite result.

The original path, starting sheet owner and diameter request index the report.
An inconclusive result retains its successful prefix and stopping evidence. -/
opaque aBackwardAttempt (depth : Nat) :
    WorkingAttempt depth workingABackwardConnector workingABackwardConnector_withinAmbient (branchSquareRootOwner 1 1)
      :=
  DyadicBank.execute
    workingABackwardConnector workingABackwardConnector_withinAmbient (branchSquareRootOwner 1 1) depth
    workingRootDiameter workingRootDiameter_positive

/-- Execute the left A boundary at the requested depth and retain its finite result.

The original path, starting sheet owner and diameter request index the report.
An inconclusive result retains its successful prefix and stopping evidence. -/
opaque aLeftBoundaryAttempt (depth : Nat) :
    WorkingAttempt depth workingLeftBoundary workingLeftBoundary_withinAmbient (branchSquareRootOwner 0 1) :=
  DyadicBank.execute
    workingLeftBoundary workingLeftBoundary_withinAmbient (branchSquareRootOwner 0 1) depth
    workingRootDiameter workingRootDiameter_positive

/-- Execute the forward B connector at the requested depth and retain its finite result.

The original path, starting sheet owner and diameter request index the report.
An inconclusive result retains its successful prefix and stopping evidence. -/
opaque bForwardAttempt (depth : Nat) :
    WorkingAttempt depth workingBConnector workingBConnector_withinAmbient (branchSquareRootOwner 0 0) :=
  DyadicBank.execute
    workingBConnector workingBConnector_withinAmbient (branchSquareRootOwner 0 0) depth
    workingRootDiameter workingRootDiameter_positive

/-- Execute the backward B connector at the requested depth and retain its finite result.

The original path, starting sheet owner and diameter request index the report.
An inconclusive result retains its successful prefix and stopping evidence. -/
opaque bBackwardAttempt (depth : Nat) :
    WorkingAttempt depth workingBBackwardConnector workingBBackwardConnector_withinAmbient (branchSquareRootOwner 2 1)
      :=
  DyadicBank.execute
    workingBBackwardConnector workingBBackwardConnector_withinAmbient (branchSquareRootOwner 2 1) depth
    workingRootDiameter workingRootDiameter_positive

/-! ## Measured prepared cycles -/

/-- Assemble the four independently measured A-cycle banks. -/
@[expose] def executedABoundaryData
    (forward : WorkingBank connectorInnerDepth
      workingAConnector
      (branchSquareRootOwner 0 0))
    (rightBoundary : WorkingBank
      rightBoundaryInnerDepth workingRightBoundary
      (branchSquareRootOwner 1 0))
    (backward : WorkingBank connectorInnerDepth
      workingABackwardConnector
      (branchSquareRootOwner 1 1))
    (leftBoundary : WorkingBank
      leftBoundaryInnerDepth workingLeftBoundary
      (branchSquareRootOwner 0 1)) :
    Topology.PreparedCycleModels.PreparedBoundaryDoublePath LoopBaseBranches.baseCurve :=
  { leftAmbient := Hyperelliptic.Branches.Cuts.Ambient LoopBaseBranches.baseCurve
    rightAmbient := Hyperelliptic.Branches.Cuts.Ambient LoopBaseBranches.baseCurve
    connectorAmbient := Hyperelliptic.Branches.Cuts.Ambient LoopBaseBranches.baseCurve
    leftState := branchState 0
    rightState := branchState 1
    connector := workingAConnector
    rightBoundaryPath := workingRightBoundary
    leftBoundaryPath := workingLeftBoundary
    forwardDepth := connectorInnerDepth
    rightBoundaryDepth := rightBoundaryInnerDepth
    backwardDepth := connectorInnerDepth
    leftBoundaryDepth := leftBoundaryInnerDepth
    rootDiameter := workingRootDiameter
    rootDiameterPositive := workingRootDiameter_positive
    forwardOwner := branchSquareRootOwner 0 0
    forwardChecked := forward
    rightBoundaryOwner := branchSquareRootOwner 1 0
    rightBoundaryChecked := rightBoundary
    backwardOwner := branchSquareRootOwner 1 1
    backwardChecked := backward
    leftBoundaryOwner := branchSquareRootOwner 0 1
    leftBoundaryChecked := leftBoundary }

/-- The unsubdivided owner-boundary cycle represented by the prepared
loop-base A-cycle data. -/
@[expose] def rawACycleTarget (_ : Unit) :
    Path.Gaussian.Lifted.Closed.ClosedLiftedPath 2 :=
  Hyperelliptic.Branches.BranchCutLifts.doubleLiftWithBoundaryOwners
    (branchState 0) (branchState 1)
      (rawConnector 0 1)

set_option genInjectivity false in
/-- Prepared loop-base cycle data cached together with its raw geometric
realization.  Carrying the dependent proof with the executable data avoids
reconstructing the large bank value during downstream elaboration. -/
structure RealizedPreparedCycle
    (raw : Path.Gaussian.Lifted.Closed.ClosedLiftedPath 2) where
  /-- The retained executable prepared-cycle data for the original Legendre curve. -/ data :
    Topology.PreparedCycleModels.PreparedCycleData LoopBaseBranches.baseCurve
  /-- The exact raw-cycle realization of the retained prepared data. -/ realizes :
    Topology.PreparedCycleModels.PreparedCycleData.RealizesRaw data raw

constructive_injectivity RealizedPreparedCycle

set_option genInjectivity false in
/-- The four successful measured banks which make up the displayed A cycle.
Keeping them in one payload gives downstream programs one owner for the
finite work instead of six independently callable opaque computations. -/
structure PreparedABanks where
  /-- The successful measured A forward connector bank, indexed by its original path, depth and starting owner. -/
    forward : WorkingBank connectorInnerDepth
    workingAConnector
    (branchSquareRootOwner 0 0)
  /-- The successful measured A right boundary bank, indexed by its original path, depth and starting owner. -/
    rightBoundary : WorkingBank
    rightBoundaryInnerDepth workingRightBoundary
    (branchSquareRootOwner 1 0)
  /-- The successful measured A backward connector bank, indexed by its original path, depth and starting owner. -/
    backward : WorkingBank connectorInnerDepth
    workingABackwardConnector
    (branchSquareRootOwner 1 1)
  /-- The successful measured A left boundary bank, indexed by its original path, depth and starting owner. -/
    leftBoundary : WorkingBank
    leftBoundaryInnerDepth workingLeftBoundary
    (branchSquareRootOwner 0 1)

constructive_injectivity PreparedABanks

/-- The first measured A bank whose executable construction failed. -/
inductive ABankFailureStage
  /-- The measured A forward connector bank was the first unsuccessful finite attempt. -/ | forward
  /-- The measured A right boundary bank was the first unsuccessful finite attempt. -/ | rightBoundary
  /-- The measured A backward connector bank was the first unsuccessful finite attempt. -/ | backward
  /-- The measured A left boundary bank was the first unsuccessful finite attempt. -/ | leftBoundary
deriving DecidableEq
derive_exposed_repr ABankFailureStage

set_option genInjectivity false in
/-- The first unfinished A-cycle bank attempt with its earlier completed banks.

The original execution retains the failed path's reusable prefix and stopping
reason. Earlier banks remain available instead of being acquired again. -/
inductive ABankFailure where
  /-- The forward attempt stopped after the retained earlier banks. -/
  | forward
      (attempt : WorkingAttempt connectorInnerDepth workingAConnector workingAConnector_withinAmbient
        (branchSquareRootOwner 0 0))
      (unfinished : attempt.bank? = none)
  /-- The rightBoundary attempt stopped after the retained earlier banks. -/
  | rightBoundary
      (forward : WorkingBank connectorInnerDepth workingAConnector (branchSquareRootOwner 0 0))
      (attempt : WorkingAttempt rightBoundaryInnerDepth workingRightBoundary workingRightBoundary_withinAmbient
        (branchSquareRootOwner 1 0))
      (unfinished : attempt.bank? = none)
  /-- The backward attempt stopped after the retained earlier banks. -/
  | backward
      (forward : WorkingBank connectorInnerDepth workingAConnector (branchSquareRootOwner 0 0))
      (rightBoundary : WorkingBank rightBoundaryInnerDepth workingRightBoundary (branchSquareRootOwner 1 0))
      (attempt : WorkingAttempt connectorInnerDepth workingABackwardConnector workingABackwardConnector_withinAmbient
        (branchSquareRootOwner 1 1))
      (unfinished : attempt.bank? = none)
  /-- The leftBoundary attempt stopped after the retained earlier banks. -/
  | leftBoundary
      (forward : WorkingBank connectorInnerDepth workingAConnector (branchSquareRootOwner 0 0))
      (rightBoundary : WorkingBank rightBoundaryInnerDepth workingRightBoundary (branchSquareRootOwner 1 0))
      (backward : WorkingBank connectorInnerDepth workingABackwardConnector (branchSquareRootOwner 1 1))
      (attempt : WorkingAttempt leftBoundaryInnerDepth workingLeftBoundary workingLeftBoundary_withinAmbient
        (branchSquareRootOwner 0 1))
      (unfinished : attempt.bank? = none)

namespace ABankFailure

/-- Read the stage of the retained first incomplete attempt. -/
@[expose] def stage : ABankFailure → ABankFailureStage
  | .forward _ _ => .forward
  | .rightBoundary _ _ _ => .rightBoundary
  | .backward _ _ _ _ => .backward
  | .leftBoundary _ _ _ _ _ => .leftBoundary

end ABankFailure

namespace PreparedABanks

/-- Assemble the cached A-bank payload into its prepared boundary path. -/
@[expose] def boundaryData (banks : PreparedABanks) :=
  executedABoundaryData banks.forward banks.rightBoundary banks.backward
    banks.leftBoundary

/-- The cached A banks together with the already proved raw-cycle
realization they determine. -/
@[expose] def witness (banks : PreparedABanks) :
    RealizedPreparedCycle (rawACycleTarget ()) :=
  let boundary := banks.boundaryData
  { data := .finiteCut boundary
    realizes := by
      simpa only [boundary, PreparedABanks.boundaryData,
        executedABoundaryData, rawACycleTarget,
          rawConnector, branchState,
        branchIndex] using
        (Topology.PreparedCycleModels.PreparedCycleData.RealizesRaw.finiteCutDyadicScheduled
          boundary (rawConnector 0 1)
          (rawConnector_withinAmbient 0 1)
          aConnectorOuterDepths (by
            change workingAConnector = _
            rfl)
          (rawBoundary_withinAmbient 1)
          rightBoundaryOuterDepths (by
            change workingRightBoundary = _
            rfl)
          (rawBoundary_withinAmbient 0)
          leftBoundaryOuterDepths (by
            change workingLeftBoundary = _
            rfl)) }

end PreparedABanks

/-- Execute the displayed A banks in dependency order and retain the first unfinished report.

Earlier completed banks and the failed execution's prefix are retained; the
existing total-cycle fallback is still selected only by its original caller. -/
@[expose] def attemptPreparedABanks (_ : Unit) : Except ABankFailure PreparedABanks :=
  let attempt := aForwardAttempt connectorInnerDepth
  match unfinished : attempt.bank? with
  | none => .error (.forward attempt unfinished)
  | some forward =>
      let attempt := aRightBoundaryAttempt rightBoundaryInnerDepth
      match unfinished : attempt.bank? with
      | none => .error (.rightBoundary forward attempt unfinished)
      | some rightBoundary =>
          let attempt := aBackwardAttempt connectorInnerDepth
          match unfinished : attempt.bank? with
          | none => .error (.backward forward rightBoundary attempt unfinished)
          | some backward =>
              let attempt := aLeftBoundaryAttempt leftBoundaryInnerDepth
              match unfinished : attempt.bank? with
              | none => .error (.leftBoundary forward rightBoundary backward attempt unfinished)
              | some leftBoundary =>
                  .ok { forward, rightBoundary, backward, leftBoundary }

/-- Conservative total A-cycle construction retained as a proof-producing
fallback if an explicitly bounded execution reports failure. -/
@[expose] def totalPreparedACycleWitness (_ : Unit) :
    RealizedPreparedCycle (rawACycleTarget ()) := by
  let boundary :=
    Topology.PreparedCycleModels.PreparedBoundaryDoublePath.ofConnectorAtWithOwners
      (LoopBaseBranches.baseBranchData ()) LoopBaseBranches.baseCurve_degree_gt_one
        (branchIndex 0)
      (branchIndex 1) 0
      (branchSquareRootOwner 0 0)
        (branchSquareRootOwner 1 0)
      (branchSquareRootOwner 1 1)
        (branchSquareRootOwner 0 1)
  exact
    { data := .finiteCut boundary
      realizes := by
        unfold rawACycleTarget rawConnector
          branchState
        exact .finiteCut boundary rfl rfl }

/-- Data projection of the conservative A-cycle witness. -/
@[expose] def totalPreparedACycle (token : Unit) :
    Topology.PreparedCycleModels.PreparedCycleData LoopBaseBranches.baseCurve :=
  (totalPreparedACycleWitness token).data

/-- Canonical cached A-cycle witness, preferring the measured executable
banks and retaining the constructive total fallback. -/
@[expose] def preparedACycleWitness (token : Unit) :
    RealizedPreparedCycle (rawACycleTarget ()) :=
  match attemptPreparedABanks token with
  | .ok banks => banks.witness
  | .error _failure => totalPreparedACycleWitness token

/-- The explicit A cut prefers the measured executable banks while remaining
total by the general finite preparation theorem. -/
@[expose] def preparedACycle (token : Unit) :
    Topology.PreparedCycleModels.PreparedCycleData LoopBaseBranches.baseCurve :=
  (preparedACycleWitness token).data

/-- Assemble the two measured B-cycle connector banks. -/
@[expose] def executedBDoubleData
    (forward : WorkingBank bConnectorInnerDepth
      workingBConnector
      (branchSquareRootOwner 0 0))
    (backward : WorkingBank bConnectorInnerDepth
      workingBBackwardConnector
        (branchSquareRootOwner 2 1)) :
    Topology.PreparedCycleModels.PreparedDoublePath LoopBaseBranches.baseCurve :=
  { ambient := Hyperelliptic.Branches.Cuts.Ambient LoopBaseBranches.baseCurve
    start := (branchState 0).box.anchor
    finish := (branchState 2).box.anchor
    basePath := workingBConnector
    depth := bConnectorInnerDepth
    rootDiameter := workingRootDiameter
    rootDiameterPositive := workingRootDiameter_positive
    forwardOwner := branchSquareRootOwner 0 0
    forwardChecked := forward
    backwardOwner := branchSquareRootOwner 2 1
    backwardChecked := backward }

/-- The unsubdivided double lift represented by the prepared loop-base
B-cycle data. -/
@[expose] def rawBCycleTarget (_ : Unit) :
    Path.Gaussian.Lifted.Closed.ClosedLiftedPath 2 :=
  Hyperelliptic.Branches.BranchCutLifts.doubleLift (rawConnector 0 2)

set_option genInjectivity false in
/-- The two successful measured banks which make up the displayed B cycle. -/
structure PreparedBBanks where
  /-- The successful measured B forward connector bank, indexed by its original path, depth and starting owner. -/
    forward : WorkingBank bConnectorInnerDepth
    workingBConnector
    (branchSquareRootOwner 0 0)
  /-- The successful measured B backward connector bank, indexed by its original path, depth and starting owner. -/
    backward : WorkingBank bConnectorInnerDepth
    workingBBackwardConnector (branchSquareRootOwner
      2 1)

constructive_injectivity PreparedBBanks

/-- The first measured B bank whose executable construction failed. -/
inductive BBankFailureStage
  /-- The measured B forward connector bank was the first unsuccessful finite attempt. -/ | forward
  /-- The measured B backward connector bank was the first unsuccessful finite attempt. -/ | backward
deriving DecidableEq
derive_exposed_repr BBankFailureStage

set_option genInjectivity false in
/-- The first unfinished B-cycle bank attempt with its earlier completed banks.

The original execution retains the failed path's reusable prefix and stopping
reason. Earlier banks remain available instead of being acquired again. -/
inductive BBankFailure where
  /-- The forward attempt stopped after the retained earlier banks. -/
  | forward
      (attempt : WorkingAttempt bConnectorInnerDepth workingBConnector workingBConnector_withinAmbient
        (branchSquareRootOwner 0 0))
      (unfinished : attempt.bank? = none)
  /-- The backward attempt stopped after the retained earlier banks. -/
  | backward
      (forward : WorkingBank bConnectorInnerDepth workingBConnector (branchSquareRootOwner 0 0))
      (attempt : WorkingAttempt bConnectorInnerDepth workingBBackwardConnector workingBBackwardConnector_withinAmbient
        (branchSquareRootOwner 2 1))
      (unfinished : attempt.bank? = none)

namespace BBankFailure

/-- Read the stage of the retained first incomplete attempt. -/
@[expose] def stage : BBankFailure → BBankFailureStage
  | .forward _ _ => .forward
  | .backward _ _ _ => .backward

end BBankFailure

namespace PreparedBBanks

/-- Assemble the cached B-bank payload into its prepared double path. -/
@[expose] def doubleData (banks : PreparedBBanks) :=
  executedBDoubleData banks.forward banks.backward

/-- The cached B banks together with the raw-cycle realization they
determine. -/
@[expose] def witness (banks : PreparedBBanks) :
    RealizedPreparedCycle (rawBCycleTarget ()) :=
  let bridge := banks.doubleData
  { data := .bridge bridge
    realizes :=
      .bridgeDyadicScheduled bridge (rawConnector 0 2)
        (rawConnector_withinAmbient 0 2)
          bConnectorOuterDepths (by
          change workingBConnector = _
          rfl) }

end PreparedBBanks

/-- Execute the displayed B banks in dependency order and retain the first unfinished report.

Earlier completed banks and the failed execution's prefix are retained; the
existing total-cycle fallback is still selected only by its original caller. -/
@[expose] def attemptPreparedBBanks (_ : Unit) : Except BBankFailure PreparedBBanks :=
  let attempt := bForwardAttempt bConnectorInnerDepth
  match unfinished : attempt.bank? with
  | none => .error (.forward attempt unfinished)
  | some forward =>
      let attempt := bBackwardAttempt bConnectorInnerDepth
      match unfinished : attempt.bank? with
      | none => .error (.backward forward attempt unfinished)
      | some backward =>
          .ok { forward, backward }

/-- Conservative total B-cycle construction retained as a fallback. -/
@[expose] def totalPreparedBCycleWitness (_ : Unit) :
    RealizedPreparedCycle (rawBCycleTarget ()) := by
  let bridge :=
    Topology.PreparedCycleModels.PreparedDoublePath.ofConnectorAtWithOwners
      (LoopBaseBranches.baseBranchData ()) LoopBaseBranches.baseCurve_degree_gt_one
        (branchIndex 0)
      (branchIndex 2) 0
      (branchSquareRootOwner 0 0)
        (branchSquareRootOwner 2 1)
  exact
    { data := .bridge bridge
      realizes := by
        unfold rawBCycleTarget rawConnector
          branchState
        exact .bridge bridge }

/-- Data projection of the conservative B-cycle witness. -/
@[expose] def totalPreparedBCycle (token : Unit) :
    Topology.PreparedCycleModels.PreparedCycleData LoopBaseBranches.baseCurve :=
  (totalPreparedBCycleWitness token).data

/-- Canonical cached B-cycle witness, preferring the measured executable
banks and retaining the constructive total fallback. -/
@[expose] def preparedBCycleWitness (token : Unit) :
    RealizedPreparedCycle (rawBCycleTarget ()) :=
  match attemptPreparedBBanks token with
  | .ok banks => banks.witness
  | .error _failure => totalPreparedBCycleWitness token

/-- The explicit B bridge, with the total finite theorem as fallback. -/
@[expose] def preparedBCycle (token : Unit) :
    Topology.PreparedCycleModels.PreparedCycleData LoopBaseBranches.baseCurve :=
  (preparedBCycleWitness token).data

set_option genInjectivity false in
/-- One runtime owner for the two independent measured bank attempts and
their total theorem-facing witnesses.  The A and B thunks are deliberately
separate: an A-only normalization request cannot force either B bank. -/
structure PreparedLegendreContext where
  /-- The independently delayed measured A-bank attempt, retaining its first failure stage. -/ aAttempt : Thunk (Except
    ABankFailure PreparedABanks)
  /-- The independently delayed measured B-bank attempt, retaining its first failure stage. -/ bAttempt : Thunk (Except
    BBankFailure PreparedBBanks)
  /-- The delayed total A-cycle witness sharing the measured A attempt and its fallback. -/ aWitness : Thunk
    (RealizedPreparedCycle (rawACycleTarget ()))
  /-- The delayed total B-cycle witness sharing the measured B attempt and its fallback. -/ bWitness : Thunk
    (RealizedPreparedCycle (rawBCycleTarget ()))

constructive_injectivity PreparedLegendreContext

/-- Allocate, but do not force, the measured A and B bank computations.  The
total witness thunks share the corresponding attempt thunk, so a successful
measured payload is never reconstructed and a failed attempt falls back only
when a theorem-facing total witness is actually requested. -/
@[expose] def preparedLegendreContext (_ : Unit) : PreparedLegendreContext :=
  let aAttempt : Thunk (Except ABankFailure
    PreparedABanks) :=
    ⟨fun _ => attemptPreparedABanks ()⟩
  let bAttempt : Thunk (Except BBankFailure
    PreparedBBanks) :=
    ⟨fun _ => attemptPreparedBBanks ()⟩
  { aAttempt
    bAttempt
    aWitness := aAttempt.map fun result =>
      match result with
      | .ok banks => banks.witness
      | .error _stage => totalPreparedACycleWitness ()
    bWitness := bAttempt.map fun result =>
      match result with
      | .ok banks => banks.witness
      | .error _stage => totalPreparedBCycleWitness () }

namespace PreparedLegendreContext

/-- Force the measured A attempt while retaining its precise failure stage. -/
@[expose] def measuredA (context : PreparedLegendreContext) := context.aAttempt.get

/-- Force the measured B attempt while retaining its precise failure stage. -/
@[expose] def measuredB (context : PreparedLegendreContext) := context.bAttempt.get

/-- Force the total A witness.  If `measuredA` has already run, this reuses
its cached payload. -/
@[expose] def preparedA (context : PreparedLegendreContext) := context.aWitness.get

/-- Force the total B witness independently of the A thunk. -/
@[expose] def preparedB (context : PreparedLegendreContext) := context.bWitness.get

end PreparedLegendreContext

/-- The branch-cut family determined by the original Legendre curve and its three branch owners. -/
@[expose] def branchFamily (_ : Unit) :=
  Hyperelliptic.Branches.BranchCutLifts.familyOfData LoopBaseBranches.baseCurve
    (LoopBaseBranches.baseBranchData ())

/-- The canonical lifted A-cycle equals the original boundary double lift of the raw connector. -/
private theorem canonicalACycle_eq_rawData :
    (((branchFamily ()).symplecticCycles.aCycle (0 : Fin 1)).liftedPath 0) =
      Hyperelliptic.Branches.BranchCutLifts.doubleLiftWithBoundaryOwners
        (branchState 0) (branchState 1)
          (rawConnector 0 1) := by
  unfold branchFamily
  rw [Hyperelliptic.Branches.BranchCutLifts.canonicalACycle_liftedPath_ofData]
  rfl

/-- The prepared A-cycle realizes the canonical lifted A basis cycle. -/
theorem preparedACycle_realizes_basis (token : Unit) :
    Topology.PreparedCycleModels.PreparedCycleData.RealizesRaw
      (preparedACycle token)
      (((branchFamily ()).symplecticCycles.aCycle (0 : Fin 1)).liftedPath 0) := by
  rw [canonicalACycle_eq_rawData]
  exact (preparedACycleWitness token).realizes

/-- Provenance of the retained connector-only certificate, not the standard B tour. -/
theorem preparedBCycle_realizes_connector (token : Unit) :
    Topology.PreparedCycleModels.PreparedCycleData.RealizesRaw
      (preparedBCycle token)
      (rawBCycleTarget token) :=
  (preparedBCycleWitness token).realizes

/-- The context-retained prepared A witness realizes the canonical lifted A basis cycle. -/
theorem preparedAOfContext_realizes_basis
    (context : PreparedLegendreContext) :
    Topology.PreparedCycleModels.PreparedCycleData.RealizesRaw
      context.preparedA.data
      (((branchFamily ()).symplecticCycles.aCycle (0 : Fin 1)).liftedPath 0) := by
  rw [canonicalACycle_eq_rawData]
  exact context.preparedA.realizes

/-- The context-retained prepared B witness realizes the original connector double lift. -/
theorem preparedBOfContext_realizes_connector
    (context : PreparedLegendreContext) :
    Topology.PreparedCycleModels.PreparedCycleData.RealizesRaw
      context.preparedB.data
      (rawBCycleTarget ()) :=
  context.preparedB.realizes

/-! ## Explicit period schedule -/

/-- Exact nonstationary cell count of the displayed measured A geometry,
computed without constructing any prepared bank. -/
@[expose] def aPeriodPreflightParentCount : Nat :=
  2 ^ connectorInnerDepth *
    workingAConnector.segmentCount +
    (2 ^ rightBoundaryInnerDepth *
      workingRightBoundary.segmentCount +
      (2 ^ connectorInnerDepth *
          workingABackwardConnector.segmentCount +
        2 ^ leftBoundaryInnerDepth *
          workingLeftBoundary.segmentCount))

/-- Bank-independent fixed-grid preflight data for the measured A cycle.
The token keeps even this small finite fold out of executable startup. -/
@[expose] def aPeriodPreflightBounds (_ : Unit) :
    Integration.PreparedSwitchedRefinements.CycleSourcePreflightBounds :=
  let source := Periods.PeriodMatrix.standardDifferential (0 : Fin 1)
  let count : Fraction.Rational :=
    Fraction.Cast.fromInt (Int.ofNat aPeriodPreflightParentCount)
  let totalWeight :=
    Integration.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
        source workingRootDiameter
          connectorInnerDepth workingAConnector +
      (Integration.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
          source workingRootDiameter
            rightBoundaryInnerDepth
            workingRightBoundary +
        (Integration.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
            source workingRootDiameter
              connectorInnerDepth
              workingABackwardConnector +
          Integration.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
            source workingRootDiameter
              leftBoundaryInnerDepth
              workingLeftBoundary))
  let integralNormSqSum :=
    Integration.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
        source workingRootDiameter
          connectorInnerDepth workingAConnector +
      (Integration.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
          source workingRootDiameter
            rightBoundaryInnerDepth
            workingRightBoundary +
        (Integration.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
            source workingRootDiameter
              connectorInnerDepth
              workingABackwardConnector +
          Integration.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
            source workingRootDiameter
              leftBoundaryInnerDepth
              workingLeftBoundary))
  { aggregateBound := count * totalWeight
    initialSampleNormSqBound := count * integralNormSqSum }

/-- All five measured A preflight scalars retained in one evaluated record. -/
@[expose] def aPeriodPreflightSummary (token : Unit) :
    Integration.PreparedSwitchedRefinements.CycleSourcePreflightSummary :=
  (aPeriodPreflightBounds token).summary

/-- The explicit A-cycle schedule owned by one retained bank context. -/
@[expose] def aPeriodScheduleOfContext (context : PreparedLegendreContext) :
    Integration.PreparedRefinementProgramCore.StandardSwitchedClosedSchedule
      LoopBaseBranches.baseCurve where
  source := Periods.PeriodMatrix.standardDifferential (0 : Fin 1)
  prepared := context.preparedA.data

/-- The explicit A-cycle schedule can be requested independently of the
full symplectic pair.  This is the shortest executable path to the sole
matrix entry needed by genus-one normalization. -/
@[expose] def aPeriodSchedule (token : Unit) :=
  aPeriodScheduleOfContext (preparedLegendreContext
    token)

/-- The centered A-period program of the retained Legendre context.

The original A schedule supplies its exact cycle and certified differential
program. Its models and certificates remain tied to that same context. -/
@[expose] def centeredAPeriodProgramOfContext
    (context : PreparedLegendreContext) :
    CertifiedPeriodProgram LoopBaseBranches.baseCurve
      (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).cycle :=
  (aPeriodScheduleOfContext context).certifiedPeriodProgram (0 : Fin 1)

/-- Certified `dx/y` program on the explicit A-cycle, with compact preflight
scalars.  The actual finite models and uniform differential certificates are
unchanged, while requesting normalization no longer evaluates their initial
coefficient centres merely to obtain a global sample bound. -/
@[expose] def aPeriodProgramOfContext (context : PreparedLegendreContext) :
    CertifiedPeriodProgram LoopBaseBranches.baseCurve
      (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).cycle where
  integral :=
    Integration.PreparedSwitchedRefinements.compactSourceIntegral LoopBaseBranches.baseCurve
      (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).prepared
  certificates := by
    intro index
    exact (centeredAPeriodProgramOfContext context).certificates index

/-- Direct refinement index selected by the ordinary public sampler for one
explicit A-period request.  Naming this reindexing here lets both finite
lower certificates and retryable normalization use the same exact state. -/
@[expose] def aPeriodModelIndex (context : PreparedLegendreContext)
    (sampleIndex : Nat) : Nat :=
  let program := aPeriodProgramOfContext context
  Gaussian.Process.Sampling.stateAt program.integral.approximation.toProcess
    (show program.integral.approximation.toProcess.State from (0 : Nat))
      sampleIndex

/-- Chunkable literal rational certificate for the exact direct refinement
state selected by one public A-period sample.  Its concrete payload can be
generated and checked in small pieces without exposing the thousands of
prepared cells in downstream theorem statements. -/
abbrev APeriodPositiveLiteralRealLowerCertificate
    (context : PreparedLegendreContext) (sampleIndex : Nat) :=
  Integration.PreparedSwitchedRefinements.CompactSourcePositiveLiteralRealLowerCertificate
    LoopBaseBranches.baseCurve (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).prepared
        (aPeriodModelIndex context sampleIndex)

/-- The literal certificate bounds the canonical compact model selected by
the same public A-period request. -/
theorem APeriodPositiveLiteralRealLowerCertificate.lower_le_model
    {context : PreparedLegendreContext} {sampleIndex : Nat}
    (certificate : APeriodPositiveLiteralRealLowerCertificate
      context sampleIndex) :
    certificate.lower <=
      (Integration.PreparedSwitchedRefinements.compactSourceModel
        (Integration.PreparedSwitchedRefinements.compactSourceState LoopBaseBranches.baseCurve
          (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
          (aPeriodScheduleOfContext context).prepared)
        (aPeriodModelIndex context sampleIndex)).integralSample.re :=
  Integration.PreparedSwitchedRefinements.CompactSourcePositiveLiteralRealLowerCertificate.lower_le_model
    certificate

/-- Sign-aware rational lower endpoint for the real part of the explicit
A-period sample selected by one public request. -/
@[expose] def aPeriodSampleRealLower (context : PreparedLegendreContext)
    (sampleIndex : Nat) : Fraction.Rational :=
  Integration.PreparedSwitchedRefinements.compactSourceIntegralRealLower
    LoopBaseBranches.baseCurve (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).prepared
        (aPeriodModelIndex context sampleIndex)

/-- Sharp sign-aware real endpoint obtained from the coefficient process
balls retained at the selected public A-period sample. -/
@[expose] def aPeriodSampleBallRealLower (context : PreparedLegendreContext)
    (sampleIndex : Nat) : Fraction.Rational :=
  Integration.PreparedSwitchedRefinements.compactSourceBallIntegralRealLower
    LoopBaseBranches.baseCurve (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).prepared
        (aPeriodModelIndex context sampleIndex)

/-- The displayed finite box endpoint bounds the real coordinate of the
corresponding public A-period sample. -/
theorem aPeriodSampleRealLower_le
    (context : PreparedLegendreContext) (sampleIndex : Nat) :
    aPeriodSampleRealLower context sampleIndex <=
      ((Gaussian.Name.Sampling.approximation
        (aPeriodProgramOfContext context).output.name).sample sampleIndex).re := by
  exact
    Integration.PreparedSwitchedRefinements.compactSourceIntegralRealLower_le_model
      LoopBaseBranches.baseCurve (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
        (aPeriodScheduleOfContext context).prepared
        (aPeriodModelIndex context sampleIndex) rfl

/-- The retained coefficient-ball real lower endpoint bounds the same public A-period sample. -/
theorem aPeriodSampleBallRealLower_le
    (context : PreparedLegendreContext) (sampleIndex : Nat) :
    aPeriodSampleBallRealLower context sampleIndex <=
      ((Gaussian.Name.Sampling.approximation
        (aPeriodProgramOfContext context).output.name).sample sampleIndex).re := by
  exact
    Integration.PreparedSwitchedRefinements.compactSourceBallIntegralRealLower_le_model
      LoopBaseBranches.baseCurve (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
        (aPeriodScheduleOfContext context).prepared
        (aPeriodModelIndex context sampleIndex) rfl

/-- Rational lower endpoint for an arbitrary fixed projection of the explicit
A-period sample selected by one public request. -/
@[expose] def aPeriodSampleDirectionalLower (context : PreparedLegendreContext)
    (direction : Gaussian.Basic.Canonical) (sampleIndex : Nat) : Fraction.Rational :=
  Integration.PreparedSwitchedRefinements.compactSourceDirectionalIntegralLower
    LoopBaseBranches.baseCurve (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).prepared direction
        (aPeriodModelIndex context sampleIndex)

/-- Sharp arbitrary-direction endpoint from the retained coefficient process
balls at one public A-period sample. -/
@[expose] def aPeriodSampleBallDirectionalLower (context : PreparedLegendreContext)
    (direction : Gaussian.Basic.Canonical) (sampleIndex : Nat) : Fraction.Rational :=
  Integration.PreparedSwitchedRefinements.compactSourceBallDirectionalIntegralLower
    LoopBaseBranches.baseCurve (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).prepared direction
        (aPeriodModelIndex context sampleIndex)

/-- The displayed directional endpoint bounds the corresponding projection
of the public A-period sample. -/
theorem aPeriodSampleDirectionalLower_le
    (context : PreparedLegendreContext) (direction : Gaussian.Basic.Canonical)
    (sampleIndex : Nat) :
    aPeriodSampleDirectionalLower context direction sampleIndex <=
      direction.re *
          ((Gaussian.Name.Sampling.approximation
            (aPeriodProgramOfContext context).output.name).sample
              sampleIndex).re +
        direction.im *
          ((Gaussian.Name.Sampling.approximation
            (aPeriodProgramOfContext context).output.name).sample
              sampleIndex).im := by
  exact
    Integration.PreparedSwitchedRefinements.compactSourceDirectionalIntegralLower_le_model
      LoopBaseBranches.baseCurve (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
        (aPeriodScheduleOfContext context).prepared direction
        (aPeriodModelIndex context sampleIndex) rfl

/-- The retained coefficient-ball directional lower endpoint bounds the matching projection of the public A-period
sample. -/
theorem aPeriodSampleBallDirectionalLower_le
    (context : PreparedLegendreContext) (direction : Gaussian.Basic.Canonical)
    (sampleIndex : Nat) :
    aPeriodSampleBallDirectionalLower context direction sampleIndex <=
      direction.re *
          ((Gaussian.Name.Sampling.approximation
            (aPeriodProgramOfContext context).output.name).sample
              sampleIndex).re +
        direction.im *
          ((Gaussian.Name.Sampling.approximation
            (aPeriodProgramOfContext context).output.name).sample
              sampleIndex).im := by
  exact
    Integration.PreparedSwitchedRefinements.compactSourceBallDirectionalIntegralLower_le_model
      LoopBaseBranches.baseCurve (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
        (aPeriodScheduleOfContext context).prepared direction
          (aPeriodModelIndex context sampleIndex) rfl

/-- Finite lazy A-state prefix owned by one retained Legendre context. -/
abbrev APeriodCache (context : PreparedLegendreContext) (count : Nat) :=
  Integration.PreparedSwitchedRefinements.CompactSourceCache LoopBaseBranches.baseCurve
    (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
    (aPeriodScheduleOfContext context).prepared count

/-- Allocate, without forcing, the A refinement states below `count`. -/
@[expose] def aPeriodCacheOfContext (context : PreparedLegendreContext) (count : Nat)
  :
    APeriodCache context count :=
  Integration.PreparedSwitchedRefinements.CompactSourceCache.canonical
    LoopBaseBranches.baseCurve (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).prepared count

/-- Certified A-period program backed by an explicitly retained finite state
prefix.  The path certificates are transported along the cache's canonical
model equality; no geometric proof is recomputed. -/
@[expose] def aPeriodProgramOfCache (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count) :
    CertifiedPeriodProgram LoopBaseBranches.baseCurve
      (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).cycle where
  integral :=
    Integration.PreparedSwitchedRefinements.compactSourceIntegralOfCache
      LoopBaseBranches.baseCurve (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
        (aPeriodScheduleOfContext context).prepared cache
  certificates := by
    intro index
    change Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates
      LoopBaseBranches.baseCurve
      (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
      (cache.model index).cells
      ((aPeriodScheduleOfContext context).cycle.liftedPath index).path
    rw [cache.model_eq_compactSourceModel]
    exact (centeredAPeriodProgramOfContext context).certificates index

/-- The explicit A-period real lower endpoint read through a retained direct
state cache.  When the public sample's direct index lies in the cache, both
the sample and this endpoint force the identical stored thunk. -/
@[expose] def aPeriodSampleRealLowerOfCache (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (sampleIndex : Nat) : Fraction.Rational :=
  cache.integralRealLower (aPeriodModelIndex context sampleIndex)

/-- Sharp real endpoint read through the retained direct-state cache. -/
@[expose] def aPeriodSampleBallRealLowerOfCache (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (sampleIndex : Nat) : Fraction.Rational :=
  cache.ballIntegralRealLower (aPeriodModelIndex context sampleIndex)

/-- Directional A-period endpoint read through the retained direct-state
cache selected by the same public sample request. -/
@[expose] def aPeriodSampleDirectionalLowerOfCache
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (direction : Gaussian.Basic.Canonical) (sampleIndex : Nat) : Fraction.Rational :=
  cache.directionalIntegralLower direction
    (aPeriodModelIndex context sampleIndex)

/-- Sharp directional endpoint read through the retained direct-state cache. -/
@[expose] def aPeriodSampleBallDirectionalLowerOfCache
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (direction : Gaussian.Basic.Canonical) (sampleIndex : Nat) : Fraction.Rational :=
  cache.ballDirectionalIntegralLower direction
    (aPeriodModelIndex context sampleIndex)

/-- Reading the real endpoint through a cache does not change its exact
rational value. -/
theorem aPeriodSampleRealLowerOfCache_eq
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (sampleIndex : Nat) :
    aPeriodSampleRealLowerOfCache context cache sampleIndex =
      aPeriodSampleRealLower context sampleIndex := by
  exact cache.integralRealLower_eq_compactSourceIntegralRealLower
    (aPeriodModelIndex context sampleIndex)

/-- Reading the coefficient-ball real endpoint through the retained cache preserves its exact rational value. -/
theorem aPeriodSampleBallRealLowerOfCache_eq
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (sampleIndex : Nat) :
    aPeriodSampleBallRealLowerOfCache context cache sampleIndex =
      aPeriodSampleBallRealLower context sampleIndex := by
  exact cache.ballIntegralRealLower_eq_compactSourceBallIntegralRealLower
    (aPeriodModelIndex context sampleIndex)

/-- Runtime sharing does not change the exact directional endpoint. -/
theorem aPeriodSampleDirectionalLowerOfCache_eq
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (direction : Gaussian.Basic.Canonical) (sampleIndex : Nat) :
    aPeriodSampleDirectionalLowerOfCache context cache direction sampleIndex =
      aPeriodSampleDirectionalLower context direction sampleIndex := by
  exact cache.directionalIntegralLower_eq_compactSourceDirectionalIntegralLower
    direction (aPeriodModelIndex context sampleIndex)

/-- Reading the coefficient-ball directional endpoint through the retained cache preserves its exact rational value. -/
theorem aPeriodSampleBallDirectionalLowerOfCache_eq
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (direction : Gaussian.Basic.Canonical) (sampleIndex : Nat) :
    aPeriodSampleBallDirectionalLowerOfCache context cache direction
        sampleIndex =
      aPeriodSampleBallDirectionalLower context direction sampleIndex := by
  exact
    cache.ballDirectionalIntegralLower_eq_compactSourceBallDirectionalIntegralLower
      direction (aPeriodModelIndex context sampleIndex)

/-- The cached endpoint bounds the cached direct model selected by the public
sample index.  The acquisition layer identifies this direct index with its
cached public sampler state. -/
theorem aPeriodSampleRealLowerOfCache_le_model
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (sampleIndex : Nat) :
    aPeriodSampleRealLowerOfCache context cache sampleIndex <=
      (cache.model (aPeriodModelIndex context sampleIndex)).integralSample.re := by
  exact cache.integralRealLower_le_model
    (aPeriodModelIndex context sampleIndex) rfl

/-- The cached coefficient-ball real endpoint bounds the same cached model selected by the public sample index. -/
theorem aPeriodSampleBallRealLowerOfCache_le_model
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (sampleIndex : Nat) :
    aPeriodSampleBallRealLowerOfCache context cache sampleIndex <=
      (cache.model (aPeriodModelIndex context sampleIndex)).integralSample.re := by
  exact cache.ballIntegralRealLower_le_model
    (aPeriodModelIndex context sampleIndex) rfl

/-- The cached directional endpoint bounds the matching projection of the
cached direct model. -/
theorem aPeriodSampleDirectionalLowerOfCache_le_model
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (direction : Gaussian.Basic.Canonical) (sampleIndex : Nat) :
    aPeriodSampleDirectionalLowerOfCache context cache direction sampleIndex <=
      direction.re *
          (cache.model (aPeriodModelIndex context sampleIndex)).integralSample.re +
        direction.im *
          (cache.model (aPeriodModelIndex context sampleIndex)).integralSample.im :=
            by
  exact cache.directionalIntegralLower_le_model direction
    (aPeriodModelIndex context sampleIndex) rfl

/-- The cached coefficient-ball directional endpoint bounds the matching projection of the same cached model. -/
theorem aPeriodSampleBallDirectionalLowerOfCache_le_model
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (direction : Gaussian.Basic.Canonical) (sampleIndex : Nat) :
    aPeriodSampleBallDirectionalLowerOfCache context cache direction
        sampleIndex <=
      direction.re *
          (cache.model
            (aPeriodModelIndex context sampleIndex)).integralSample.re +
        direction.im *
          (cache.model
            (aPeriodModelIndex context sampleIndex)).integralSample.im := by
  exact cache.ballDirectionalIntegralLower_le_model direction
    (aPeriodModelIndex context sampleIndex) rfl

/-- A positive real endpoint yields a squared-norm lower bound for the same
public A-period sample. -/
theorem aPeriodSampleRealLower_sq_le_normSq
    (context : PreparedLegendreContext) (sampleIndex : Nat)
    (positive : 0 < aPeriodSampleRealLower context sampleIndex) :
    aPeriodSampleRealLower context sampleIndex ^ 2 <=
      Norm.Basic.normSq
        ((Gaussian.Name.Sampling.approximation
          (aPeriodProgramOfContext context).output.name).sample sampleIndex) := by
  let value :=
    (Gaussian.Name.Sampling.approximation
      (aPeriodProgramOfContext context).output.name).sample sampleIndex
  have realLower : aPeriodSampleRealLower context sampleIndex <= value.re :=
    aPeriodSampleRealLower_le context sampleIndex
  calc
    aPeriodSampleRealLower context sampleIndex ^ 2 <= value.re ^ 2 :=
      Fraction.Order.Arithmetic.pow_le_pow_direct positive.le realLower 2
    _ <= Norm.Basic.normSq value := by
      unfold Norm.Basic.normSq
      exact le_add_of_nonneg_right
        (Fraction.Order.Arithmetic.sq_nonneg_direct value.im)

/-- Compatibility entry point which allocates one private retained context. -/
@[expose] def aPeriodProgram (token : Unit) :
    CertifiedPeriodProgram LoopBaseBranches.baseCurve
      (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodSchedule token).cycle :=
  aPeriodProgramOfContext (preparedLegendreContext
    token)

/-- The matching B-cycle schedule remains independent until a normalized
period observation actually requests the B entry. -/
@[expose] def bPeriodScheduleOfContext (context : PreparedLegendreContext) :
    Integration.PreparedRefinementProgramCore.StandardSwitchedClosedSchedule
      LoopBaseBranches.baseCurve where
  source := Periods.PeriodMatrix.standardDifferential (0 : Fin 1)
  prepared := context.preparedB.data

/-- The B-period schedule obtained from one newly allocated retained context. -/
@[expose] def bPeriodSchedule (token : Unit) :=
  bPeriodScheduleOfContext (preparedLegendreContext
    token)

/-- The certified centered B-period program of the retained context.

The independent B schedule supplies its exact cycle and differential program.
Reading this program retains the original context and its cached B schedule. -/
@[expose] def centeredBPeriodProgramOfContext
    (context : PreparedLegendreContext) :
    CertifiedPeriodProgram LoopBaseBranches.baseCurve
      (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
      (bPeriodScheduleOfContext context).cycle :=
  (bPeriodScheduleOfContext context).certifiedPeriodProgram (0 : Fin 1)

/-- Compact-preflight counterpart for the independently delayed B period. -/
@[expose] def bPeriodProgramOfContext (context : PreparedLegendreContext) :
    CertifiedPeriodProgram LoopBaseBranches.baseCurve
      (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
      (bPeriodScheduleOfContext context).cycle where
  integral :=
    Integration.PreparedSwitchedRefinements.compactSourceIntegral LoopBaseBranches.baseCurve
      (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
      (bPeriodScheduleOfContext context).prepared
  certificates := by
    intro index
    exact (centeredBPeriodProgramOfContext context).certificates index

/-- The certified B-period program obtained from one newly allocated retained context. -/
@[expose] def bPeriodProgram (token : Unit) :
    CertifiedPeriodProgram LoopBaseBranches.baseCurve
      (Periods.PeriodMatrix.standardDifferential (0 : Fin 1))
      (bPeriodSchedule token).cycle :=
  bPeriodProgramOfContext (preparedLegendreContext
    token)

/-- Retained numerical fixture cycles. The B banks describe the explicit
connector retrace, not the standard B tour. -/
@[expose] def fixtureCyclesOfContext (context : PreparedLegendreContext) :
    Path.Gaussian.Lifted.Family.PairedCycleRefinements 2 1 where
  aCycle := fun _ => (aPeriodScheduleOfContext context).cycle
  bCycle := fun _ => (bPeriodScheduleOfContext context).cycle

/-- Numerical fixture programs owned by one retained bank context. Projecting
the A entry leaves the independent connector B thunk unforced. -/
@[expose] def fixturePeriodDataOfContext (context : PreparedLegendreContext) :
    Periods.PeriodMatrix.PeriodData LoopBaseBranches.baseCurve where
  cycles := fixtureCyclesOfContext context
  aProgram := by
    intro differential cycle
    rcases differential with ⟨differential, differentialBound⟩
    cases differential with
    | zero =>
      rcases cycle with ⟨cycle, cycleBound⟩
      cases cycle with
      | zero => exact aPeriodProgramOfContext context
      | succ cycle =>
        exact False.elim (Nat.not_lt_zero cycle (Nat.lt_of_succ_lt_succ cycleBound))
    | succ differential =>
      exact False.elim (Nat.not_lt_zero differential
        (Nat.lt_of_succ_lt_succ differentialBound))
  bProgram := by
    intro differential cycle
    rcases differential with ⟨differential, differentialBound⟩
    cases differential with
    | zero =>
      rcases cycle with ⟨cycle, cycleBound⟩
      cases cycle with
      | zero => exact bPeriodProgramOfContext context
      | succ cycle =>
        exact False.elim (Nat.not_lt_zero cycle (Nat.lt_of_succ_lt_succ cycleBound))
    | succ differential =>
      exact False.elim (Nat.not_lt_zero differential
        (Nat.lt_of_succ_lt_succ differentialBound))

/-- Period data whose A entry reads through a retained finite cache.  The B
entry remains independently delayed and unchanged. -/
@[expose] def fixturePeriodDataOfContextWithACache (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count) :
    Periods.PeriodMatrix.PeriodData LoopBaseBranches.baseCurve where
  cycles := fixtureCyclesOfContext context
  aProgram := by
    intro differential cycle
    rcases differential with ⟨differential, differentialBound⟩
    cases differential with
    | zero =>
      rcases cycle with ⟨cycle, cycleBound⟩
      cases cycle with
      | zero => exact aPeriodProgramOfCache context cache
      | succ cycle =>
        exact False.elim (Nat.not_lt_zero cycle (Nat.lt_of_succ_lt_succ cycleBound))
    | succ differential =>
      exact False.elim (Nat.not_lt_zero differential
        (Nat.lt_of_succ_lt_succ differentialBound))
  bProgram := by
    intro differential cycle
    rcases differential with ⟨differential, differentialBound⟩
    cases differential with
    | zero =>
      rcases cycle with ⟨cycle, cycleBound⟩
      cases cycle with
      | zero => exact bPeriodProgramOfContext context
      | succ cycle =>
        exact False.elim (Nat.not_lt_zero cycle (Nat.lt_of_succ_lt_succ cycleBound))
    | succ differential =>
      exact False.elim (Nat.not_lt_zero differential
        (Nat.lt_of_succ_lt_succ differentialBound))

/-- Canonical period construction for the base fibre. Existing measured-bank
checkpoints remain available through the explicitly named fixture interfaces. -/
@[expose] def periodSchedule (_token : Unit) :
    RootClosedPeriodBank
      LoopBaseBranches.baseCurve :=
  RootClosedPeriodBank.ofData
    LoopBaseBranches.baseCurve (LoopBaseBranches.baseBranchData ())

/-- The period programs of the canonical root-closed bank for the base Legendre curve. -/
@[expose] def periodData (_token : Unit) :
    Periods.PeriodMatrix.PeriodData LoopBaseBranches.baseCurve :=
  (periodSchedule ()).periodData

/-- The one-by-one A matrix projected from a retained context. -/
@[expose] def aMatrixOfContext (context : PreparedLegendreContext) :
    Periods.PeriodMatrix.NamedMatrix 1 :=
  SquareMatrix.matrixOfFn fun _differential _cycle =>
    (aPeriodProgramOfContext context).output

/-- The one-by-one A matrix backed by a retained finite state prefix. -/
@[expose] def aMatrixOfContextWithCache (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count) :
    Periods.PeriodMatrix.NamedMatrix 1 :=
  SquareMatrix.matrixOfFn fun _differential _cycle =>
    (aPeriodProgramOfCache context cache).output

/-- The A matrix read through the retained cache equals the A projection of the same fixture period data. -/
theorem aMatrixOfContextWithCache_eq_periodData
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count) :
    aMatrixOfContextWithCache context cache =
      (fixturePeriodDataOfContextWithACache context cache).aMatrix := by
  apply SquareMatrix.matrix_ext
  intro differential cycle
  refine Data.Fin.cases_induction ?_ (fun empty => Fin.elim0 empty) differential
  refine Data.Fin.cases_induction (by rfl) (fun empty => Fin.elim0 empty) cycle

/-- The A-only projection agrees exactly with the A matrix of the complete
period pair.  Keeping the smaller definition executable prevents the B
schedule from being constructed during normalization preflight. -/
theorem aMatrixOfContext_eq_periodData
    (context : PreparedLegendreContext) :
    aMatrixOfContext context =
      (fixturePeriodDataOfContext context).aMatrix := by
  apply SquareMatrix.matrix_ext
  intro differential cycle
  refine Data.Fin.cases_induction ?_ (fun empty => Fin.elim0 empty) differential
  refine Data.Fin.cases_induction (by rfl) (fun empty => Fin.elim0 empty) cycle

/-- The A matrix of the root-closed standard period programs. -/
@[expose] def aMatrix (token : Unit) :
    Periods.PeriodMatrix.NamedMatrix 1 :=
  (periodData token).aMatrix

/-- The explicit prepared programs realize the symplectic branch-cut basis
generated from the same three rational branch owners. -/
theorem periodData_realizes_basis :
    Integration.PreparedRefinementPrograms.SymplecticCycleRealization
      LoopBaseBranches.baseCurve (periodData ()).cycles
        (Hyperelliptic.Branches.BranchCutLifts.symplecticBasisOfData
          LoopBaseBranches.baseCurve (LoopBaseBranches.baseBranchData ())).cycles :=
  Integration.PreparedRefinementPrograms.SymplecticCycleRealization.ofData
    LoopBaseBranches.baseCurve (LoopBaseBranches.baseBranchData ())

end Purelib.Examples.Curves.Legendre.Prepared.LoopBase

end
