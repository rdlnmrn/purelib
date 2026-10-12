module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.RootIsolation.FTA.Squarefree.Approximation
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.CCL.Semantics
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.RootIsolation.FTA.Positive.CCL.Basic
public import Purelib.RootIsolation.FTA.Positive.CCL.Build
import Purelib.RootIsolation.Newton.Band.Build
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Newton.Build
import Purelib.RootIsolation.Track.Newton.Refinement

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.RootContinuation.CoherentRoot
import Init.Data.Fin.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.FTA.Positive.Input
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.Roots.CCL.Terminal.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves

open Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.Rat

open Purelib.Polynomial.Dense.Gaussian.Basic

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Polynomial.Elimination.Axis

open Purelib.Riemann.RootContinuation

open Purelib.RootIsolation

open Purelib.RootIsolation.FTA.Positive

open Purelib.RootIsolation.FTA.Positive.CCL

open Purelib.RootIsolation.Newton.Band

open Purelib.RootIsolation.State

open Purelib.RootIsolation.Track.Newton

@[expose] public section

/-!
# Finite branch-point isolation for hyperelliptic curves

The squarefree certificate already stored in a `HyperellipticCurve` is fed
directly to the project-owned finite box theorem.  The result is a single
exact terminal in degree one or a degree-indexed family of pairwise-separated
shrinking tracks in higher degree.  Every site has one persistent arithmetic
CCL name and every finite prefix has exact parser semantics.
-/

namespace Purelib.Curves.Hyperelliptic.Branches.BranchIsolation

open Purelib.Riemann.Curves.AlgebraicDifferentials

/-- A productive finite Gaussian name with exact process semantics. -/
abbrev Named := Gaussian.Name.Basic.Named
/-- A productive Gaussian name carrying finite coherence evidence. -/
abbrev CoherentNamed := Coherent.CoherentNamed
/-- Exact Gaussian rational branch coordinates. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- The retained finite isolation result for a positive-degree Gaussian polynomial. -/
abbrev PositiveResult (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :=
  CCL.Basic.PositiveResult polynomial

/-- Both admitted hyperelliptic degree shapes have positive degree. -/
theorem degreePositive {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    0 < curve.polynomial.natDegree := by
  cases curve.degreeShape with
  | odd degreeEqual =>
      rw [degreeEqual]
      omega0
  | even degreeEqual =>
      rw [degreeEqual]
      omega0

/-- Automatically run finite squarefree branch isolation on the defining polynomial. -/
def branchIsolation {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    Curves.Hyperelliptic.Branches.BranchIsolation.PositiveResult curve.polynomial :=
  Build.provePositive
    { squarefree := curve.squarefree
      degreePositive := Curves.Hyperelliptic.Branches.BranchIsolation.degreePositive curve }

/-- Number of displayed finite branch sites in a unified positive-degree isolation result. -/
def siteCount {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : Curves.Hyperelliptic.Branches.BranchIsolation.PositiveResult polynomial) : Nat :=
  match result with
  | .terminal _ _ => 1
  | .higher _ _ => polynomial.natDegree

section
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
/-- The displayed branch-site count equals the degree of the original polynomial. -/
theorem siteCount_eq_natDegree {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : Curves.Hyperelliptic.Branches.BranchIsolation.PositiveResult polynomial) :
    siteCount result = polynomial.natDegree := by
  cases result with
  | terminal terminal degree =>
      exact degree.symm
  | higher boxes degree =>
      rfl

/-- A finite index into the sites of the retained isolation result. -/
abbrev SiteIndex {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : Curves.Hyperelliptic.Branches.BranchIsolation.PositiveResult polynomial) := Fin (siteCount result)

end

/-- Uniform persistent arithmetic name of a finite branch site. A linear terminal is named by its exact rational point;
a higher-degree site uses the corresponding shrinking winding-one track. -/
def siteName {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : Curves.Hyperelliptic.Branches.BranchIsolation.PositiveResult polynomial) :
      Curves.Hyperelliptic.Branches.BranchIsolation.SiteIndex result -> Named :=
  match result with
  | .terminal terminal _ => fun _ =>
      Named.exact terminal.point
  | .higher boxes _ => fun index => boxes.arithmeticNameAt index

/-- Coherent arithmetic name of the same finite branch site. Higher-degree sites use one deterministic nested anchor
sequence; the linear terminal is the exact rational name. -/
def siteCoherentName {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : Curves.Hyperelliptic.Branches.BranchIsolation.PositiveResult polynomial) :
      Curves.Hyperelliptic.Branches.BranchIsolation.SiteIndex result -> CoherentNamed :=
  match result with
  | .terminal terminal _ => fun _ =>
      Coherence.exact terminal.point
  | .higher boxes _ => fun index =>
      CoherentRoot.named (boxes.trackAt index)

/-- A displayed rational anchor for each finite site. In higher degree it is the anchor of the site's initial isolated
box; the persistent name refines that same box rather than replacing the site. -/
def siteAnchor {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : Curves.Hyperelliptic.Branches.BranchIsolation.PositiveResult polynomial) :
      Curves.Hyperelliptic.Branches.BranchIsolation.SiteIndex result -> Gaussian :=
  match result with
  | .terminal terminal _ => fun _ => terminal.point
  | .higher boxes _ => fun index => (boxes.trackAt index).initial.box.anchor

/-- Every branch site produces exactly every requested finite prefix. -/
theorem siteName_productive {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : Curves.Hyperelliptic.Branches.BranchIsolation.PositiveResult polynomial) (index :
      Curves.Hyperelliptic.Branches.BranchIsolation.SiteIndex result)
    (count : Nat) :
    (Curves.Hyperelliptic.Branches.BranchIsolation.siteName result index).machine.emitted.IsPrefix
        (Advance.advance
          (Curves.Hyperelliptic.Branches.BranchIsolation.siteName result index).machine count).emitted /\
      (Advance.advance
        (Curves.Hyperelliptic.Branches.BranchIsolation.siteName result index).machine count).emitted.length = count :=
  (Curves.Hyperelliptic.Branches.BranchIsolation.siteName result index).productive count

/-- Every emitted branch prefix retains exact finite parser semantics for the same initial terminal or root box. -/
theorem siteName_exact {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : Curves.Hyperelliptic.Branches.BranchIsolation.PositiveResult polynomial) (index :
      Curves.Hyperelliptic.Branches.BranchIsolation.SiteIndex result)
    (count : Nat) :
    Semantics.Basic.ExactCursor
      (Curves.Hyperelliptic.Branches.BranchIsolation.siteName result index).process
        (Curves.Hyperelliptic.Branches.BranchIsolation.siteName result index).state
      (Advance.advance
        (Curves.Hyperelliptic.Branches.BranchIsolation.siteName result index).machine count) :=
  CCL.Semantics.Named.advance_exact
    (Curves.Hyperelliptic.Branches.BranchIsolation.siteName result index) count

/-- Pairwise separation evidence. The degree-one branch is empty because `Fin 1` has no distinct pair; the higher branch
returns the actual separated initial root boxes. -/
def Separation {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : Curves.Hyperelliptic.Branches.BranchIsolation.PositiveResult polynomial)
    (left right : Curves.Hyperelliptic.Branches.BranchIsolation.SiteIndex result) : Prop :=
  match result with
  | .terminal _ _ => False
  | .higher boxes _ =>
      (boxes.trackAt left).initial.box.Separated
        (boxes.trackAt right).initial.box

/-- Distinct displayed branch sites have separated original isolation boxes. -/
theorem pairwiseSeparated {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : Curves.Hyperelliptic.Branches.BranchIsolation.PositiveResult polynomial)
    (left right : Curves.Hyperelliptic.Branches.BranchIsolation.SiteIndex result) (different : left ≠ right) :
    Curves.Hyperelliptic.Branches.BranchIsolation.Separation result left right := by
  cases result with
  | terminal terminal degree =>
      have equal : left = right := by
        apply Fin.ext
        have leftBound := left.isLt
        have rightBound := right.isLt
        change left.val < 1 at leftBound
        change right.val < 1 at rightBound
        omega0
      exact (different equal).elim
  | higher boxes degree =>
      exact boxes.trackAt_pairwiseSeparated left right different

/-- Distinct displayed sites have different retained Gaussian anchors. -/
theorem siteAnchor_ne {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : Curves.Hyperelliptic.Branches.BranchIsolation.PositiveResult polynomial)
    (left right : Curves.Hyperelliptic.Branches.BranchIsolation.SiteIndex result) (different : left ≠ right) :
    Curves.Hyperelliptic.Branches.BranchIsolation.siteAnchor result left ≠
      Curves.Hyperelliptic.Branches.BranchIsolation.siteAnchor result right := by
  cases result with
  | terminal terminal degree =>
      have equal : left = right := by
        apply Fin.ext
        have leftBound := left.isLt
        have rightBound := right.isLt
        change left.val < 1 at leftBound
        change right.val < 1 at rightBound
        omega0
      exact (different equal).elim
  | higher boxes degree =>
      exact (boxes.trackAt_pairwiseSeparated left right different).points_ne
        (boxes.trackAt left).initial.box.contains_anchor
        (boxes.trackAt right).initial.box.contains_anchor

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation in
set_option genInjectivity false in
/-- The original degree-complete finite family of retained branch tracks.

Persistent arithmetic and coherent names share the exact retained anchors. Higher-degree tracks keep their original
ambient square and pairwise separation, with the site count identified with the defining polynomial degree. -/
structure Data {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) where
  /-- The finite number of retained branch sites. -/ siteCount : Nat
  /-- The retained site count equals the defining polynomial degree. -/ count_eq : siteCount =
    curve.polynomial.natDegree
  /-- The persistent arithmetic name at each retained branch site. -/ nameAt : Fin siteCount ->
    Curves.Hyperelliptic.Branches.BranchIsolation.Named
  /-- The coherent arithmetic name at each retained branch site. -/ coherentNameAt : Fin siteCount ->
    Curves.Hyperelliptic.Branches.BranchIsolation.CoherentNamed
  /-- The retained exact Gaussian anchor at each site. -/ anchorAt : Fin siteCount ->
    Curves.Hyperelliptic.Branches.BranchIsolation.Gaussian
  /-- The shrinking winding-one track for each site when the defining degree exceeds one. -/ trackAt : (degreeGtOne : 1
    < curve.polynomial.natDegree) ->
    Fin siteCount ->
      Track.Basic.WindingOneTrack curve.polynomial
        (RootRadius.Box.largeSquareBox curve.polynomial)
  /-- Each track begins at the exact anchor retained for that site. -/ track_anchor_eq : forall
    (degreeGtOne : 1 < curve.polynomial.natDegree) (index : Fin siteCount),
    (trackAt degreeGtOne index).initial.box.anchor = anchorAt index
  /-- Distinct site tracks have separated initial isolation boxes. -/ trackAt_pairwiseSeparated : forall
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : Fin siteCount), left ≠ right ->
      (trackAt degreeGtOne left).initial.box.Separated
        (trackAt degreeGtOne right).initial.box

constructive_injectivity Data

/-- Convert the project-owned global finite isolator into the smaller branch interface actually used by the Riemann
modules. -/
def data {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve := by
  let result := Curves.Hyperelliptic.Branches.BranchIsolation.branchIsolation curve
  cases resultEq : result with
  | terminal terminal degree =>
      exact
        { siteCount := 1
          count_eq := degree.symm
          nameAt := fun _ =>
            Named.exact terminal.point
          coherentNameAt := fun _ =>
            Coherence.exact terminal.point
          anchorAt := fun _ => terminal.point
          trackAt := fun degreeGtOne => by
            have impossible : ¬1 < curve.polynomial.natDegree := by
              rw [degree]
              omega0
            exact (impossible degreeGtOne).elim
          track_anchor_eq := fun degreeGtOne => by
            have impossible : ¬1 < curve.polynomial.natDegree := by
              rw [degree]
              omega0
            exact (impossible degreeGtOne).elim
          trackAt_pairwiseSeparated := fun degreeGtOne => by
            have impossible : ¬1 < curve.polynomial.natDegree := by
              rw [degree]
              omega0
            exact (impossible degreeGtOne).elim }
  | higher boxes degree =>
      exact
        { siteCount := curve.polynomial.natDegree
          count_eq := rfl
          nameAt := boxes.arithmeticNameAt
          coherentNameAt := fun index =>
            CoherentRoot.named (boxes.trackAt index)
          anchorAt := fun index => (boxes.trackAt index).initial.box.anchor
          trackAt := fun _ index => boxes.trackAt index
          track_anchor_eq := fun _ _ => rfl
          trackAt_pairwiseSeparated := fun _ left right different =>
            boxes.trackAt_pairwiseSeparated left right different }

/-- Build branch data directly from a displayed degree-indexed family of pairwise-separated shrinking winding-one
tracks. This is the finite input form used by small worked examples and externally audited isolations. -/
def Data.ofTracks {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (_degreeGtOne : 1 < curve.polynomial.natDegree)
    (tracks : Fin curve.polynomial.natDegree ->
      Track.Basic.WindingOneTrack curve.polynomial
        (RootRadius.Box.largeSquareBox curve.polynomial))
    (pairwise : forall left right, left ≠ right ->
      (tracks left).initial.box.Separated (tracks right).initial.box) :
    Curves.Hyperelliptic.Branches.BranchIsolation.Data curve where
  siteCount := curve.polynomial.natDegree
  count_eq := rfl
  nameAt := fun index =>
    (CoherentRoot.named (tracks index)).name
  coherentNameAt := fun index => CoherentRoot.named (tracks index)
  anchorAt := fun index => (tracks index).initial.box.anchor
  trackAt := fun _ index => tracks index
  track_anchor_eq := fun _ _ => rfl
  trackAt_pairwiseSeparated := fun _ left right different =>
    pairwise left right different

/-- Extend one fully displayed winding-one state to a total shrinking track. Unlike `trackOfRaw`, this constructor
performs no preliminary extraction; the caller has already supplied the four ambient-line clearances needed by
branch-cut construction. -/
def trackOfState {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (initial : WindingOne.Basic.WindingOneState curve.polynomial
      (RootRadius.Box.largeSquareBox curve.polynomial)) :
    Track.Basic.WindingOneTrack curve.polynomial
      (RootRadius.Box.largeSquareBox curve.polynomial) := by
  have degreeAtLeastTwo : 2 ≤ curve.polynomial.natDegree := by omega0
  exact
    { initial := initial
      refine := fun current epsilon positive =>
        Refinement.refineState degreeAtLeastTwo curve.squarefree
          (Separated.separatedAxisEliminationCertificate
            curve.polynomial curve.nonzero (Curves.Hyperelliptic.Branches.BranchIsolation.degreePositive curve))
          current epsilon positive
      nested := by
        intro current epsilon positive
        exact Refinement.refineState_refines degreeAtLeastTwo
          curve.squarefree
          (Separated.separatedAxisEliminationCertificate
            curve.polynomial curve.nonzero (Curves.Hyperelliptic.Branches.BranchIsolation.degreePositive curve))
          current epsilon positive
      strict := by
        intro current epsilon positive
        exact Refinement.refineState_strict degreeAtLeastTwo
          curve.squarefree
          (Separated.separatedAxisEliminationCertificate
            curve.polynomial curve.nonzero (Curves.Hyperelliptic.Branches.BranchIsolation.degreePositive curve))
          current epsilon positive
      accurate := by
        intro current epsilon positive
        exact Refinement.refineState_accurate degreeAtLeastTwo
          curve.squarefree
          (Separated.separatedAxisEliminationCertificate
            curve.polynomial curve.nonzero (Curves.Hyperelliptic.Branches.BranchIsolation.degreePositive curve))
          current epsilon positive }

/-- Assemble explicit branch data from pairwise-separated winding-one states. The original states become refinement zero
literally. -/
def Data.ofStates {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (states : Fin curve.polynomial.natDegree ->
      WindingOne.Basic.WindingOneState curve.polynomial
        (RootRadius.Box.largeSquareBox curve.polynomial))
    (pairwise : forall left right, left ≠ right ->
      (states left).box.Separated (states right).box) :
    Curves.Hyperelliptic.Branches.BranchIsolation.Data curve :=
  Curves.Hyperelliptic.Branches.BranchIsolation.Data.ofTracks curve degreeGtOne
    (fun index => Curves.Hyperelliptic.Branches.BranchIsolation.trackOfState curve degreeGtOne (states index))
    pairwise

/-- Turn one explicit nonzero-winding raw box into a total shrinking winding-one track. The Newton extraction supplies
the four ambient-line clearances required by branch-cut construction; all later refinements reuse the curve's finite
squarefree and axis-elimination certificates. -/
def trackOfRaw {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (raw : Raw.RawWindingState curve.polynomial
      (RootRadius.Box.largeSquareBox curve.polynomial)) :
    Track.Basic.WindingOneTrack curve.polynomial
      (RootRadius.Box.largeSquareBox curve.polynomial) := by
  have degreeAtLeastTwo : 2 ≤ curve.polynomial.natDegree := by omega0
  let elimination :=
    Separated.separatedAxisEliminationCertificate curve.polynomial
      curve.nonzero (Curves.Hyperelliptic.Branches.BranchIsolation.degreePositive curve)
  let output := Build.extract degreeAtLeastTwo curve.squarefree
    elimination raw (by
        decide : (0 : Fraction.Rational) < 1)
  let initial : WindingOne.Basic.WindingOneState curve.polynomial
      (RootRadius.Box.largeSquareBox curve.polynomial) :=
    { box := output.box
      refinesAmbient := output.refinesAmbient
      proper := output.proper
      clearance := output.clearance
      rawWindingFour := output.rawWindingFour
      ambientLeftClearance := output.ambientLeftClearance
      ambientRightClearance := output.ambientRightClearance
      ambientBottomClearance := output.ambientBottomClearance
      ambientTopClearance := output.ambientTopClearance }
  exact Build.ofInitial degreeAtLeastTwo curve.squarefree
    elimination initial

/-- The extracted initial winding-one box lies strictly inside the raw box from which its track was constructed. -/
theorem trackOfRaw_initial_strict {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (raw : Raw.RawWindingState curve.polynomial
      (RootRadius.Box.largeSquareBox curve.polynomial)) :
    (Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.trackOfRaw curve degreeGtOne raw).initial.box.StrictInterior
      raw.box := by
  unfold Curves.Hyperelliptic.Branches.BranchIsolation.trackOfRaw
  exact (Build.extract _ curve.squarefree _ raw _).strictCurrent

/-- Build branch data from a degree-indexed family of raw winding boxes whose interiors are pairwise disjoint. Strict
Newton extraction turns those weak interior separations into the positive closed-box gaps required downstream. -/
def Data.ofRawStates {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (raw : Fin curve.polynomial.natDegree ->
      Raw.RawWindingState curve.polynomial
        (RootRadius.Box.largeSquareBox curve.polynomial))
    (pairwise : forall left right, left ≠ right ->
      (raw left).box.InteriorSeparated (raw right).box) :
    Curves.Hyperelliptic.Branches.BranchIsolation.Data curve :=
  Curves.Hyperelliptic.Branches.BranchIsolation.Data.ofTracks curve degreeGtOne
    (fun index => Curves.Hyperelliptic.Branches.BranchIsolation.trackOfRaw curve degreeGtOne (raw index))
    (by
      intro left right different
      exact (pairwise left right different).strict_refinements
        (Curves.Hyperelliptic.Branches.BranchIsolation.trackOfRaw_initial_strict curve degreeGtOne (raw left))
        (Curves.Hyperelliptic.Branches.BranchIsolation.trackOfRaw_initial_strict curve degreeGtOne (raw right)))

namespace Data

section
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
/-- A finite index into the sites of the retained branch data. -/
abbrev Index {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : Curves.Hyperelliptic.Branches.BranchIsolation.Data curve) := Fin data.siteCount

/-- Read the persistent arithmetic name of a retained branch site. -/
def name {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : Curves.Hyperelliptic.Branches.BranchIsolation.Data curve) (index :
      Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index data) : Named :=
  data.nameAt index

/-- Read the coherent arithmetic name of a retained branch site. -/
def coherentName {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : Curves.Hyperelliptic.Branches.BranchIsolation.Data curve) (index :
      Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index data) : CoherentNamed :=
  data.coherentNameAt index

/-- Read the retained exact Gaussian anchor of a branch site. -/
def anchor {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : Curves.Hyperelliptic.Branches.BranchIsolation.Data curve) (index :
      Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index data) : Gaussian :=
  data.anchorAt index

/-- Reindex a displayed branch site by the polynomial degree. This is a definitionally finite cast justified by the
exact root count returned by the isolator. -/
def degreeIndex {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : Curves.Hyperelliptic.Branches.BranchIsolation.Data curve) (index :
      Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index data) :
    Fin curve.polynomial.natDegree :=
  Fin.cast data.count_eq index

/-- The actual shrinking track of a displayed finite branch site, available whenever the curve has higher degree. -/
def track {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : Curves.Hyperelliptic.Branches.BranchIsolation.Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (index : Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index data) :
    Track.Basic.WindingOneTrack curve.polynomial
      (RootRadius.Box.largeSquareBox curve.polynomial) :=
  data.trackAt degreeGtOne index

/-- The initial box of a retained branch track has exactly its displayed anchor. -/
theorem track_initial_anchor {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (data : Curves.Hyperelliptic.Branches.BranchIsolation.Data
      curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree) (index : Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index
      data) :
    (data.track degreeGtOne index).initial.box.anchor = data.anchor index := by
  exact data.track_anchor_eq degreeGtOne index

/-- Every retained branch-site name emits the requested finite prefix while preserving the existing prefix. -/
theorem name_productive {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : Curves.Hyperelliptic.Branches.BranchIsolation.Data curve) (index :
      Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index data) (count : Nat) :
    (Curves.Hyperelliptic.Branches.BranchIsolation.Data.name data index).machine.emitted.IsPrefix
        (Advance.advance
          (Curves.Hyperelliptic.Branches.BranchIsolation.Data.name data index).machine count).emitted /\
      (Advance.advance
        (Curves.Hyperelliptic.Branches.BranchIsolation.Data.name data index).machine count).emitted.length = count :=
  (Curves.Hyperelliptic.Branches.BranchIsolation.Data.name data index).productive count

/-- Each requested finite branch-name prefix retains exact parser semantics for its original process and state. -/
theorem name_exact {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : Curves.Hyperelliptic.Branches.BranchIsolation.Data curve) (index :
      Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index data) (count : Nat) :
    Semantics.Basic.ExactCursor
      (Curves.Hyperelliptic.Branches.BranchIsolation.Data.name data index).process
        (Curves.Hyperelliptic.Branches.BranchIsolation.Data.name data index).state
      (Advance.advance
        (Curves.Hyperelliptic.Branches.BranchIsolation.Data.name data index).machine count) :=
  CCL.Semantics.Named.advance_exact (Curves.Hyperelliptic.Branches.BranchIsolation.Data.name data index) count

/-- Distinct retained higher-degree branch tracks have separated initial boxes. -/
theorem separated {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : Curves.Hyperelliptic.Branches.BranchIsolation.Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index data) (different : left ≠ right) :
    (data.track degreeGtOne left).initial.box.Separated
      (data.track degreeGtOne right).initial.box :=
  data.trackAt_pairwiseSeparated degreeGtOne left right different

/-- Distinct retained branch sites have unequal Gaussian anchors. -/
theorem anchor_ne {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : Curves.Hyperelliptic.Branches.BranchIsolation.Data curve) (left right :
      Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index data) (different : left ≠ right) :
    Curves.Hyperelliptic.Branches.BranchIsolation.Data.anchor data left ≠
      Curves.Hyperelliptic.Branches.BranchIsolation.Data.anchor data right :=
  by
    have degreeGtOne : 1 < curve.polynomial.natDegree := by
      rw [← data.count_eq]
      by_contra small
      have countLeOne : data.siteCount <= 1 := Nat.le_of_not_gt small
      apply different
      apply Fin.ext
      have leftBound := left.isLt
      have rightBound := right.isLt
      omega0
    change data.anchorAt left ≠ data.anchorAt right
    rw [← data.track_anchor_eq degreeGtOne left,
      ← data.track_anchor_eq degreeGtOne right]
    exact (data.separated degreeGtOne left right different).points_ne
      (data.track degreeGtOne left).initial.box.contains_anchor
      (data.track degreeGtOne right).initial.box.contains_anchor

end

end Data

end Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
