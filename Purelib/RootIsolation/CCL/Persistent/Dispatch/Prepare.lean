module
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.CCL.Persistent.Dispatch.Basic
public import Purelib.RootIsolation.CCL.Persistent.Dispatch.Finite
import Purelib.RootIsolation.CCL.Persistent.State.Basic
import Purelib.RootIsolation.CCL.Persistent.Terminal.Prepare
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Exclusion.Homography

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.CCL.Parser.Formula.Input
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
import Purelib.Geometry.Projective.Hermitian.Formula.Box.Override
import Purelib.Geometry.Projective.Hermitian.Formula.Box.Stability
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.CCL.Persistent.Controller.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

public section

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Finite dispatch through initial CCL boundary ownership

One persistent controller step first separates the current box from the
single affine pole of its decoder matrix, then removes the bounded set of
rational terminals, and finally inspects the current nonterminal child
formula.  It either executes a box-stable strict-sign/equality-owned step or
retains the first genuinely parameterized Hermitian boundary with its
analysis and a uniform positive decoder-denominator margin.  Universal zero
boundaries are discharged structurally, and finite zero sets are exhausted
by a bounded form-cache loop.  Coupling the remaining curve events to the
persistent sample provider remains.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Dispatch.Prepare

/-- Execute denominator and terminal preparation, exhaust every finite
equality boundary, and either append one stable bit or return the first
genuinely parameterized curve event. -/
@[expose] def dispatch
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Track.Basic.WindingOneTrack p ambient) (current : State p ambient) :
    CCL.Persistent.Dispatch.Basic.Outcome current := by
  let parser := Data.CCL.Encoding.Parser.State.parse current.word
  let inverse := LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate.adjugate parser.matrix
  have inverseDeterminantNonzero :
      LinearAlgebra.Coordinates2.Matrix.Matrix2.determinant inverse ≠ 0 := by
    change LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate.determinant
      (LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate.adjugate parser.matrix) ≠ 0
    rw [LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate.determinant_adjugate]
    simpa only [parser, LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate.determinant, -eq_self, -iff_self] using
      Data.CCL.Encoding.Parser.State.parse_det_ne current.word
  match Track.Exclusion.Homography.decide degreePositive track
      current.numerical inverse
      (LinearAlgebra.Coordinates2.Matrix.Boundary.lowerRow_ne_of_determinant_ne inverse
        inverseDeterminantNonzero) with
  | .exact point root inside _denominatorZero =>
      exact .decided (.exact ⟨point, root, inside⟩)
  | .separated separated =>
    let separatedState := current.refine separated.state separated.refines
    match CCL.Persistent.Terminal.Prepare.prepare degreePositive track
        separatedState with
    | .exact root =>
      exact .decided (.exact
        { point := root.point
          root := root.root
          inside := separated.refines.contains root.inside })
    | .ready localPrepared =>
      let prepared : CCL.Persistent.Terminal.Prepare.SourcePersistentDispatchPreparedAlias current :=
        { state := localPrepared.state
          boxRefines := localPrepared.boxRefines.trans separated.refines
          word_eq := by
            simpa only [separatedState,
              State.refine_word, -eq_self, -iff_self] using
              localPrepared.word_eq
          canContinue := localPrepared.canContinue }
      let denominator : CCL.Persistent.Dispatch.Basic.DenominatorCertificate prepared :=
        { margin := separated.margin
          margin_pos := separated.margin_pos
          lower := by
            intro value inside
            have lower := separated.lower
              (localPrepared.boxRefines.contains inside)
            have wordIdentity : prepared.state.word = current.word :=
              prepared.word_eq
            simpa only [wordIdentity, parser, inverse, -eq_self, -iff_self] using lower }
      exact CCL.Persistent.Dispatch.Finite.dispatchFinite degreePositive track
        ⟨prepared, denominator, CCL.Persistent.Dispatch.Finite.candidateForms prepared.state.word, [], (by
          intro bit atom member
          exact Or.inl (CCL.Persistent.Dispatch.Finite.form_mem_candidateForms
            prepared.state.word bit member))⟩

end Purelib.RootIsolation.CCL.Persistent.Dispatch.Prepare

end
