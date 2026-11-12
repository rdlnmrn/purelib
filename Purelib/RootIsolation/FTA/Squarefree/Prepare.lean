module

import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.RootIsolation.Exact.Basic
public import Purelib.RootIsolation.Exact.LargeSquare
import Purelib.RootIsolation.Exact.Ownership.Cardinality
public import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free box-only finite constructive FTA

This is the paper-facing numerical layer over the explicit constructive
fraction and Gaussian representations.  The squarefree certificate is finite
dense extended-Euclid data.  Both axis eliminants are computed internally by
the fraction-free separated Sylvester construction.
-/

namespace Purelib.RootIsolation.FTA.Squarefree.Input

open Purelib.Polynomial.Dense.Gaussian.Basic
section Input

/-- The exact finite degree bound of the two internally computed axis
eliminants. -/
def eliminationDegree {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  (_input : Input p) : Nat :=
  Elimination.Axis.Separated.separatedEliminationDegree p

/-- Closed finite axis-elimination certificate computed from `p`'s displayed
coefficient list. -/
def elimination {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input
  : Input p) :
    Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p
      input.eliminationDegree :=
  Elimination.Axis.Separated.separatedAxisEliminationCertificate p
    input.nonzero input.degreePositive

/-- The complete original elimination cache reads the original degree bound from its same two retained polynomials. -/
theorem elimination_degree_eq
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input : Input p)
    (cached : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p input.eliminationDegree)
    (same : cached = input.elimination) : cached.degree = input.eliminationDegree :=
  (congrArg Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate.degree same).trans (by rfl)

/-- Exact degree-many isolation in the coefficient-computed large square. -/
def isolation {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input :
  Input p) (request : Option Data.Rat.Fraction.Rational := none) :
    Exact.Basic.Output p
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) p.natDegree :=
  Exact.LargeSquare.isolateLargeSquare input.degreeAtLeastTwo
    input.squarefree input.elimination request

/-- Every selected coefficient-produced root retains its complete original Newton constructor. -/
theorem isolation_trackAt_origin
    {p : CanonicalCoefficients.CoefficientPolynomial} (input : Input p)
    (request : Option Data.Rat.Fraction.Rational) (index : Fin p.natDegree) :
    Track.Newton.Build.Origin input.degreeAtLeastTwo input.squarefree input.elimination
      ((input.isolation request).trackAt index) :=
  Exact.LargeSquare.isolateLargeSquare_tracks_origin input.degreeAtLeastTwo input.squarefree input.elimination
    request ((input.isolation request).trackAt index)
    (List.get_mem (input.isolation request).tracks ((input.isolation request).trackIndex index))

/-- The actual original isolated track consumes the same retained input elimination at each refinement request. -/
theorem isolation_trackAt_refine
    {p : CanonicalCoefficients.CoefficientPolynomial} (input : Input p)
    (request : Option Data.Rat.Fraction.Rational) (index : Fin p.natDegree)
    (current : State.WindingOne.Basic.WindingOneState p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p))
    (epsilon : Data.Rat.Fraction.Rational) (positive : 0 < epsilon) :
    ((input.isolation request).trackAt index).refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive :=
  Track.Newton.Build.Origin.refine (input.isolation_trackAt_origin request index) current epsilon positive

set_option genInjectivity false in
/-- The original squarefree input with its once-computed elimination and exact isolation.

Both complete constructor equalities retain the original input and its
coefficient-computed large square. Ownership construction and restored
checkpoints consume these same caches rather than running isolation again. -/
structure Prepared {p : CanonicalCoefficients.CoefficientPolynomial} (input : Input p)
    (request : Option Data.Rat.Fraction.Rational := none) where
  /-- The actual original axis-elimination certificate. -/ elimination :
    Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p input.eliminationDegree
  /-- The elimination is the complete original coefficient computation. -/ elimination_eq :
    elimination = input.elimination
  /-- The exact original isolation computed using the retained elimination. -/ isolation :
    Exact.Basic.Output p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) p.natDegree
  /-- The isolation is the complete original finite extraction result. -/ isolation_eq :
    isolation = Exact.LargeSquare.isolateLargeSquare input.degreeAtLeastTwo input.squarefree elimination request

constructive_injectivity Prepared

namespace Prepared

/-- Restore the same original preparation from a checked elimination and complete isolation result. -/
def ofIsolation {p : CanonicalCoefficients.CoefficientPolynomial} (input : Input p)
    {request : Option Data.Rat.Fraction.Rational}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p input.eliminationDegree)
    (eliminationEq : elimination = input.elimination)
    (isolation : Exact.Basic.Output p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) p.natDegree)
    (isolationEq : isolation =
      Exact.LargeSquare.isolateLargeSquare input.degreeAtLeastTwo input.squarefree elimination request) :
    Prepared input request :=
  ⟨elimination, eliminationEq, isolation, isolationEq⟩

/-- The retained exact isolation agrees with the complete original input constructor. -/
theorem isolation_eq_original {p : CanonicalCoefficients.CoefficientPolynomial}
    {input : Input p} {request : Option Data.Rat.Fraction.Rational} (prepared : Prepared input request) :
    prepared.isolation = input.isolation request := by
  exact prepared.isolation_eq.trans (congrArg
    (fun elimination => Exact.LargeSquare.isolateLargeSquare input.degreeAtLeastTwo input.squarefree elimination
      request)
    prepared.elimination_eq)

/-- Every actual retained isolation track uses the same original Newton refinement with the cached elimination. -/
theorem refine {p : CanonicalCoefficients.CoefficientPolynomial}
    {input : Input p} {request : Option Data.Rat.Fraction.Rational} (prepared : Prepared input request) :
    ∀ track ∈ prepared.isolation.tracks,
      track.refine = Track.Newton.Refinement.refineState
        input.degreeAtLeastTwo input.squarefree prepared.elimination := by
  intro track member
  rw [prepared.isolation_eq] at member
  rcases Exact.LargeSquare.isolateLargeSquare_tracks_origin input.degreeAtLeastTwo input.squarefree
    prepared.elimination request track member with ⟨initial, same⟩
  exact congrArg (fun retained => retained.refine) same

end Prepared

/-- Compute elimination once and run exact isolation once with that same retained certificate. -/
def prepare {p : CanonicalCoefficients.CoefficientPolynomial} (input : Input p)
    (request : Option Data.Rat.Fraction.Rational := none) : Prepared input request :=
  let elimination := input.elimination
  let isolation := Exact.LargeSquare.isolateLargeSquare input.degreeAtLeastTwo input.squarefree elimination request
  Prepared.ofIsolation input (request := request) elimination rfl isolation rfl

/-- Degree-sharp bound for every finite pairwise-separated family of
winding-one tracks in the same large square. -/
theorem familyCardLe
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input : Input p) {familyCount :
      Nat}
    (family : Fin familyCount → Track.Basic.WindingOneTrack p
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p))
    (pairwise : ∀ left right, left ≠ right →
      (family left).initial.box.Separated
        (family right).initial.box) :
    familyCount ≤ p.natDegree :=
  Exact.Ownership.Cardinality.family_card_le_natDegree
    input.degreeAtLeastTwo input.squarefree input.elimination family pairwise

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)

set_option genInjectivity false in
/-- The original elimination certificate with its actual degree retained as executable data.

The scalar degree equality and complete certificate transport identify the
original input's constructor. Numerical consumers read the stored degree and
the same retained polynomials instead of computing the eliminants again merely
to recover their bound.
-/
structure Elimination {p : CoefficientPolynomial} (input : Input p) where
  /-- The actual maximum degree, retained independently of the original degree expression. -/ degree : Nat
  /-- The stored degree is exactly the original input's coefficient-computed bound. -/
  degree_eq : degree = input.eliminationDegree
  /-- The complete original certificate, indexed by the stored degree. -/
  certificate : AxisEliminationCertificate p degree
  /-- Degree transport retains the complete original certificate. -/
  certificate_eq : certificate.castDegree degree_eq = input.elimination

constructive_injectivity Elimination

namespace Elimination

/-- Read the same complete original certificate at the original input's bound. -/
def original {p : CoefficientPolynomial}
    {input : Input p} (cached : Elimination input) :
    AxisEliminationCertificate p input.eliminationDegree :=
  cached.certificate.castDegree cached.degree_eq

/-- The retained certificate's original-index view is the input's complete constructor. -/
theorem original_eq {p : CoefficientPolynomial}
    {input : Input p} (cached : Elimination input) : cached.original = input.elimination :=
  cached.certificate_eq

/-- Retain the degree read from the two actual cached eliminants without computing either again. -/
def ofCertificate {p : CoefficientPolynomial} (input : Input p)
    (certificate : AxisEliminationCertificate p
      input.eliminationDegree) (same : certificate = input.elimination) : Elimination input :=
  let degree := certificate.degree
  have degreeEq : degree = input.eliminationDegree := input.elimination_degree_eq certificate same
  { degree := degree
    degree_eq := degreeEq
    certificate := certificate.castDegree degreeEq.symm
    certificate_eq := (certificate.castDegree_inverse degreeEq.symm).trans same }

/-- The cached bound is read from the supplied original polynomials. -/
theorem ofCertificate_degree {p : CoefficientPolynomial} (input : Input p)
    (certificate : AxisEliminationCertificate p
      input.eliminationDegree) (same : certificate = input.elimination) :
    (ofCertificate input certificate same).degree = certificate.degree := rfl

/-- Reading the original-index view preserves the complete supplied certificate. -/
theorem ofCertificate_original {p : CoefficientPolynomial}
    (input : Input p)
    (certificate : AxisEliminationCertificate p
      input.eliminationDegree) (same : certificate = input.elimination) :
    (ofCertificate input certificate same).original = certificate :=
  certificate.castDegree_inverse (input.elimination_degree_eq certificate same).symm

/-- Compute the original certificate once and retain its actual bound alongside it. -/
def ofInput {p : CoefficientPolynomial}
    (input : Input p) : Elimination input :=
  let certificate := input.elimination
  ofCertificate input certificate rfl

/-- Any two such caches retain the same complete original data and scalar degree. -/
theorem eq_of_input {p : CoefficientPolynomial}
    {input : Input p} (left right : Elimination input) : left = right := by
  cases left with
  | mk leftDegree leftEq leftCertificate leftSame =>
      cases right with
      | mk rightDegree rightEq rightCertificate rightSame =>
          cases leftEq
          cases rightEq
          cases leftSame
          cases rightSame
          rfl

end Elimination

end Input
end Purelib.RootIsolation.FTA.Squarefree.Input

end
