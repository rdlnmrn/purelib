module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity.Index
public import Purelib.Riemann.RootContinuation.CoherentRoot.PairSeparation
public import Purelib.Riemann.RootContinuation.CoherentRoot.PointSeparation
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive.Coprime
import Purelib.Geometry.Rational.Box.Separation.Certificate
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial

/-!
# Pair separation in original multiplicity root caches

Roots of one factor use the original isolation-box separation. Roots of
distinct factors consume a retained ordered Bézout certificate, with exact
linear readings handled directly and nonlinear readings at their original
certified tail stages.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity

open Purelib.Polynomial.Dense.Gaussian.Multiplicity

open Purelib
open Purelib.RootIsolation
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Sequence.Selection (PairBound)
open Purelib.Geometry.Rational
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

namespace Realization

/-- Original owner-indexed state readers for one retained factor realization.

Exact linear factors have no state requests. A nonlinear factor keeps each
original bounded track owner and supplies complete states at their unchanged
indices, with equality to that actual cached root's state program.
-/
@[expose] def StateReaders (m : Type → Type) {entry : PositiveEntry}
    {factor : Residual.Multiplicity.Factor entry} (realization : Realization factor) : Type :=
  match factor, realization with
  | .linear .., .linear .. => PUnit
  | .higher _ preparation, .higher roots =>
      (owner : Fin preparation.boxes.isolation.tracks.length) → (index : Nat) →
        m {current : WindingOneState entry.part.polynomial
            (Bounds.RootRadius.Box.largeSquareBox entry.part.polynomial) //
          current = (roots.get owner).stateAt index}

/-- Read one original state through the exact nonlinear view projected by its retained factor realization.

The factor and bounded owner index select the same supplied state accessor.
The view's getter equality transports its original polynomial, ambient and
cached root together; no state producer or replacement root is constructed.
-/
def stateFromView {m : Type → Type} {entry : PositiveEntry} {factor : Residual.Multiplicity.Factor entry}
    (roots : Realization factor) (states : StateReaders m roots) (owner : Fin (count factor))
    (view : CertifiedName.View (roots.channel owner)) (found : roots.view? owner = some view) (index : Nat) :
    m {current : WindingOneState view.polynomial view.ambient // current = view.root.stateAt index} := by
  cases factor with
  | linear degree data inverse inverseEq =>
      cases roots with
      | linear value valueEq geometric geometricEq =>
          change none = some view at found
          cases found
  | higher degree preparation =>
      cases roots with
      | higher roots =>
          have same : CertifiedName.View.ofRoot (roots.get owner) ⟨entry.part.squarefree, entry.degreePositive⟩ =
              view := Option.some.inj found
          cases same
          exact states owner index

/-- Original roots of one retained factor keep its exact or same-isolation pair separation. -/
def pairBound {entry : PositiveEntry} {factor : Residual.Multiplicity.Factor entry}
    (roots : Realization factor) (first second : Fin (count factor)) :
    PairBound roots.approximation first second := by
  cases factor with
  | linear degree data inverseNorm inverseNorm_eq =>
    have equal : first = second := by
      apply Fin.ext
      have firstBound := first.isLt
      have secondBound := second.isLt
      change first.val < 1 at firstBound
      change second.val < 1 at secondBound
      omega0
    subst second
    exact PairBound.diagonal roots.approximation first
  | higher degree preparation =>
    cases roots with
    | higher roots =>
      if equal : first = second then
        subst second
        exact PairBound.diagonal (fun index => (roots.get index).approximation) first
      else
        let separation := Box.separationCertificate
          (preparation.boxes.isolation.tracks_get_separated first second equal)
        exact
          { leftIndex := 0
            rightIndex := 0
            gap := separation.gap ^ 2
            positive := Data.Rat.Fraction.Order.Arithmetic.pow_pos_direct separation.positive 2
            lower := fun _ firstLater secondLater _ _ =>
              (roots.get first).separation_lower (roots.get second) separation firstLater secondLater }

/-- Distinct original factors give a pair bound on their actual cached root programs.

The supplied candidate readbacks preserve both original factor-root indices.
The ordered Bézout certificate is already retained; this operation constructs
only the actual root/point separation requests and their original tail bounds.
-/
def coprimePairBound {firstEntry secondEntry : PositiveEntry}
    {firstFactor : Residual.Multiplicity.Factor firstEntry}
    {secondFactor : Residual.Multiplicity.Factor secondEntry}
    (first : Realization firstFactor) (second : Realization secondFactor)
    (coprime : Coprime.Basic.CoprimeCertificate firstEntry.part.polynomial secondEntry.part.polynomial)
    (firstRoot : Fin (count firstFactor)) (secondRoot : Fin (count secondFactor))
    {candidateCount : Nat} (candidates : Fin candidateCount → Sequence.ApproximationData)
    (left right : Fin candidateCount)
    (left_eq : candidates left = first.approximation firstRoot)
    (right_eq : candidates right = second.approximation secondRoot) : PairBound candidates left right := by
  cases firstFactor with
  | linear firstDegree firstData firstInverse firstInverse_eq =>
    cases first with
    | linear firstValue firstValue_eq firstGeometric firstGeometric_eq =>
      have leftRead : ∀ index, (candidates left).sample index = firstData.point := by
        intro index
        rewrite [left_eq]
        change firstGeometric.sample index = firstData.point
        rewrite [firstGeometric_eq]
        rfl
      have secondNonzero : secondEntry.part.polynomial.eval firstData.point ≠ 0 := by
        cases coprime.eval_ne_zero firstData.point with
        | inl nonzero => exact (nonzero firstData.root).elim
        | inr nonzero => exact nonzero
      cases secondFactor with
      | linear secondDegree secondData secondInverse secondInverse_eq =>
        cases second with
        | linear secondValue secondValue_eq secondGeometric secondGeometric_eq =>
          have rightRead : ∀ index, (candidates right).sample index = secondData.point := by
            intro index
            rewrite [right_eq]
            change secondGeometric.sample index = secondData.point
            rewrite [secondGeometric_eq]
            rfl
          have different : firstData.point - secondData.point ≠ 0 := by
            intro zero
            have equal := Basic.gaussian_eq_of_sub_eq_zero zero
            have root := secondData.root
            rewrite [← equal] at root
            exact secondNonzero root
          exact
            { leftIndex := 0
              rightIndex := 0
              gap := normSq (firstData.point - secondData.point)
              positive := Norm.Basic.normSq_pos different
              lower := by
                intro _ firstLater secondLater _ _
                rewrite [leftRead firstLater, rightRead secondLater]
                exact Data.Rat.Fraction.Order.Basic.le_refl _ }
      | higher secondDegree secondPreparation =>
        cases second with
        | higher secondRoots =>
          let certificate := PointSeparation.ofPoint (secondRoots.get secondRoot) firstData.point secondNonzero 0
          exact (certificate.toPairBound candidates right left right_eq leftRead).symm
  | higher firstDegree firstPreparation =>
    cases first with
    | higher firstRoots =>
      cases secondFactor with
      | linear secondDegree secondData secondInverse secondInverse_eq =>
        cases second with
        | linear secondValue secondValue_eq secondGeometric secondGeometric_eq =>
          have rightRead : ∀ index, (candidates right).sample index = secondData.point := by
            intro index
            rewrite [right_eq]
            change secondGeometric.sample index = secondData.point
            rewrite [secondGeometric_eq]
            rfl
          have firstNonzero : firstEntry.part.polynomial.eval secondData.point ≠ 0 := by
            cases coprime.eval_ne_zero secondData.point with
            | inl nonzero => exact nonzero
            | inr nonzero => exact (nonzero secondData.root).elim
          let certificate := PointSeparation.ofPoint (firstRoots.get firstRoot) secondData.point firstNonzero 0
          exact certificate.toPairBound candidates left right left_eq rightRead
      | higher secondDegree secondPreparation =>
        cases second with
        | higher secondRoots =>
          let certificate := PairSeparation.ofCoprime (firstRoots.get firstRoot)
            (secondRoots.get secondRoot) coprime 0 0
          exact certificate.toPairBound candidates left right left_eq right_eq

/-- Restore an original cross-factor bound through its actual retained root-state readers.

The original linear, point/root and root/root branches consume the same
ordered coprimality certificate. Nonlinear branches retain the complete
original point or pair separation, including sufficient stages and actual
cached states; exact linear branches require no state reads.
-/
def coprimePairBoundWithStates {m : Type → Type} [Monad m] {firstEntry secondEntry : PositiveEntry}
    {firstFactor : Residual.Multiplicity.Factor firstEntry}
    {secondFactor : Residual.Multiplicity.Factor secondEntry}
    (first : Realization firstFactor) (second : Realization secondFactor)
    (coprime : Coprime.Basic.CoprimeCertificate firstEntry.part.polynomial secondEntry.part.polynomial)
    (firstRoot : Fin (count firstFactor)) (secondRoot : Fin (count secondFactor))
    {candidateCount : Nat} (candidates : Fin candidateCount → Sequence.ApproximationData)
    (left right : Fin candidateCount)
    (left_eq : candidates left = first.approximation firstRoot)
    (right_eq : candidates right = second.approximation secondRoot)
    (firstStates : StateReaders m first) (secondStates : StateReaders m second) :
    m {value : PairBound candidates left right //
      value = coprimePairBound first second coprime firstRoot secondRoot candidates left right left_eq right_eq} := by
  cases firstFactor with
  | linear firstDegree firstData firstInverse firstInverse_eq =>
    cases first with
    | linear firstValue firstValue_eq firstGeometric firstGeometric_eq =>
      have leftRead : ∀ index, (candidates left).sample index = firstData.point := by
        intro index
        rewrite [left_eq]
        change firstGeometric.sample index = firstData.point
        rewrite [firstGeometric_eq]
        rfl
      have secondNonzero : secondEntry.part.polynomial.eval firstData.point ≠ 0 := by
        cases coprime.eval_ne_zero firstData.point with
        | inl nonzero => exact (nonzero firstData.root).elim
        | inr nonzero => exact nonzero
      cases secondFactor with
      | linear secondDegree secondData secondInverse secondInverse_eq =>
        cases second with
        | linear secondValue secondValue_eq secondGeometric secondGeometric_eq => exact pure ⟨_, rfl⟩
      | higher secondDegree secondPreparation =>
        cases second with
        | higher secondRoots => exact do
          let root := secondRoots.get secondRoot
          let certificate ← PointSeparation.ofValueWithStates root firstData.point
            (secondEntry.part.polynomial.eval firstData.point) rfl secondNonzero 0 (secondStates secondRoot)
          let value := (certificate.val.toPairBound candidates right left right_eq leftRead).symm
          have original : value = coprimePairBound
              (.linear firstValue firstValue_eq firstGeometric firstGeometric_eq) (.higher secondRoots)
              coprime firstRoot secondRoot candidates left right left_eq right_eq := by
            dsimp only [coprimePairBound]
            exact congrArg (fun certificate : PointSeparation root firstData.point 0 =>
              (certificate.toPairBound candidates right left right_eq leftRead).symm) certificate.property
          return ⟨value, original⟩
  | higher firstDegree firstPreparation =>
    cases first with
    | higher firstRoots =>
      cases secondFactor with
      | linear secondDegree secondData secondInverse secondInverse_eq =>
        cases second with
        | linear secondValue secondValue_eq secondGeometric secondGeometric_eq => exact do
          have rightRead : ∀ index, (candidates right).sample index = secondData.point := by
            intro index
            rewrite [right_eq]
            change secondGeometric.sample index = secondData.point
            rewrite [secondGeometric_eq]
            rfl
          have firstNonzero : firstEntry.part.polynomial.eval secondData.point ≠ 0 := by
            cases coprime.eval_ne_zero secondData.point with
            | inl nonzero => exact nonzero
            | inr nonzero => exact (nonzero secondData.root).elim
          let root := firstRoots.get firstRoot
          let certificate ← PointSeparation.ofValueWithStates root secondData.point
            (firstEntry.part.polynomial.eval secondData.point) rfl firstNonzero 0 (firstStates firstRoot)
          let value := certificate.val.toPairBound candidates left right left_eq rightRead
          have original : value = coprimePairBound (.higher firstRoots)
              (.linear secondValue secondValue_eq secondGeometric secondGeometric_eq)
              coprime firstRoot secondRoot candidates left right left_eq right_eq := by
            dsimp only [coprimePairBound]
            exact congrArg (fun certificate : PointSeparation root secondData.point 0 =>
              certificate.toPairBound candidates left right left_eq rightRead) certificate.property
          return ⟨value, original⟩
      | higher secondDegree secondPreparation =>
        cases second with
        | higher secondRoots => exact do
          let certificate ← PairSeparation.ofCoprimeWithStates (firstRoots.get firstRoot)
            (secondRoots.get secondRoot) coprime 0 0 (firstStates firstRoot) (secondStates secondRoot)
          let value := certificate.val.toPairBound candidates left right left_eq right_eq
          have original : value = coprimePairBound (.higher firstRoots) (.higher secondRoots)
              coprime firstRoot secondRoot candidates left right left_eq right_eq := by
            dsimp only [coprimePairBound]
            exact congrArg (fun certificate : PairSeparation (firstRoots.get firstRoot)
                (secondRoots.get secondRoot) 0 0 =>
              certificate.toPairBound candidates left right left_eq right_eq) certificate.property
          return ⟨value, original⟩

end Realization

namespace Family

/-- Original factor- and root-indexed readers for this same retained multiplicity family. -/
abbrev StateReaders (m : Type → Type) {entries : List PositiveEntry}
    {preparation : Residual.Multiplicity.Family entries} (roots : Family preparation) :=
  (factor : Fin entries.length) → Realization.StateReaders m (roots.get factor)

/-- Build a root-pair bound using the same stored factor-pair certificate and original occurrence indices. -/
def pairBoundFromFactors {entries : List PositiveEntry} {preparation : Residual.Multiplicity.Family entries}
    (roots : Family preparation) (factorPairs : Basis.Positive.CoprimePairs entries)
    (firstFactor secondFactor : Fin entries.length)
    (firstRoot : Fin (count (preparation.get firstFactor)))
    (secondRoot : Fin (count (preparation.get secondFactor))) :
    PairBound roots.candidates (Index.fromFactor preparation firstFactor firstRoot).toFin
      (Index.fromFactor preparation secondFactor secondRoot).toFin := by
  if equal : firstFactor = secondFactor then
    subst secondFactor
    let bound := (roots.get firstFactor).pairBound firstRoot secondRoot
    refine
      { leftIndex := bound.leftIndex
        rightIndex := bound.rightIndex
        gap := bound.gap
        positive := bound.positive
        lower := ?_ }
    intro different firstLater secondLater firstOrder secondOrder
    have rootDifferent : firstRoot ≠ secondRoot := by
      intro same
      exact different (congrArg (fun index => (Index.fromFactor preparation firstFactor index).toFin) same)
    rewrite [roots.candidates_fromFactor firstFactor firstRoot,
      roots.candidates_fromFactor firstFactor secondRoot]
    exact bound.lower rootDifferent firstLater secondLater firstOrder secondOrder
  else
    let coprime := (factorPairs.get firstFactor secondFactor).certificate equal
    exact (roots.get firstFactor).coprimePairBound (roots.get secondFactor) coprime firstRoot secondRoot
      roots.candidates (Index.fromFactor preparation firstFactor firstRoot).toFin
      (Index.fromFactor preparation secondFactor secondRoot).toFin
      (roots.candidates_fromFactor firstFactor firstRoot) (roots.candidates_fromFactor secondFactor secondRoot)

/-- Bound any original finite candidate pair using its unchanged original factor and root projections. -/
def pairBound {entries : List PositiveEntry} {preparation : Residual.Multiplicity.Family entries}
    (roots : Family preparation) (factorPairs : Basis.Positive.CoprimePairs entries)
    (firstIndex secondIndex : Fin (size preparation)) : PairBound roots.candidates firstIndex secondIndex := by
  let first := Index.ofFin preparation firstIndex
  let second := Index.ofFin preparation secondIndex
  have firstEqual : (Index.fromFactor preparation first.factorIndex first.rootIndex).toFin = firstIndex :=
    (congrArg Index.toFin (Index.fromFactor_projections first)).trans (Index.toFin_ofFin preparation firstIndex)
  have secondEqual : (Index.fromFactor preparation second.factorIndex second.rootIndex).toFin = secondIndex :=
    (congrArg Index.toFin (Index.fromFactor_projections second)).trans (Index.toFin_ofFin preparation secondIndex)
  let bound := roots.pairBoundFromFactors factorPairs first.factorIndex second.factorIndex
    first.rootIndex second.rootIndex
  rewrite [firstEqual, secondEqual] at bound
  exact bound

/-- Materialize the original root-pair certificates and cache their common original tail stage and positive gap. -/
def pairs {entries : List PositiveEntry} {preparation : Residual.Multiplicity.Family entries}
    (roots : Family preparation) (factorPairs : Basis.Positive.CoprimePairs entries) :
    Sequence.Selection.Pairs roots.candidates :=
  Sequence.Selection.Pairs.ofFn (roots.pairBound factorPairs)

/-- Restore the complete original factor-indexed bound through shared original-state readers.

Pairs in one factor retain their existing box-gap construction. Distinct
factors use the same ordered Bézout entry and actual original root indices;
only their original state reads pass through the supplied shared readers.
-/
def pairBoundFromFactorsWithStates {m : Type → Type} [Monad m] {entries : List PositiveEntry}
    {preparation : Residual.Multiplicity.Family entries} (roots : Family preparation)
    (factorPairs : Basis.Positive.CoprimePairs entries) (states : StateReaders m roots)
    (firstFactor secondFactor : Fin entries.length)
    (firstRoot : Fin (count (preparation.get firstFactor)))
    (secondRoot : Fin (count (preparation.get secondFactor))) :
    m {value : PairBound roots.candidates (Index.fromFactor preparation firstFactor firstRoot).toFin
      (Index.fromFactor preparation secondFactor secondRoot).toFin //
      value = roots.pairBoundFromFactors factorPairs firstFactor secondFactor firstRoot secondRoot} := do
  if equal : firstFactor = secondFactor then
    return ⟨_, rfl⟩
  else
    let coprime := (factorPairs.get firstFactor secondFactor).certificate equal
    let actual ← (roots.get firstFactor).coprimePairBoundWithStates (roots.get secondFactor) coprime
      firstRoot secondRoot roots.candidates (Index.fromFactor preparation firstFactor firstRoot).toFin
      (Index.fromFactor preparation secondFactor secondRoot).toFin
      (roots.candidates_fromFactor firstFactor firstRoot) (roots.candidates_fromFactor secondFactor secondRoot)
      (states firstFactor) (states secondFactor)
    have original : actual.val =
        roots.pairBoundFromFactors factorPairs firstFactor secondFactor firstRoot secondRoot := by
      dsimp only [pairBoundFromFactors]
      rewrite [dif_neg equal]
      exact actual.property
    return ⟨actual.val, original⟩

/-- Restore a complete original candidate-pair entry at its unchanged bounded matrix coordinates. -/
def pairBoundWithStates {m : Type → Type} [Monad m] {entries : List PositiveEntry}
    {preparation : Residual.Multiplicity.Family entries} (roots : Family preparation)
    (factorPairs : Basis.Positive.CoprimePairs entries) (states : StateReaders m roots)
    (firstIndex secondIndex : Fin (size preparation)) :
    m {value : PairBound roots.candidates firstIndex secondIndex //
      value = roots.pairBound factorPairs firstIndex secondIndex} := do
  let first := Index.ofFin preparation firstIndex
  let second := Index.ofFin preparation secondIndex
  have firstEqual : (Index.fromFactor preparation first.factorIndex first.rootIndex).toFin = firstIndex :=
    (congrArg Index.toFin (Index.fromFactor_projections first)).trans (Index.toFin_ofFin preparation firstIndex)
  have secondEqual : (Index.fromFactor preparation second.factorIndex second.rootIndex).toFin = secondIndex :=
    (congrArg Index.toFin (Index.fromFactor_projections second)).trans (Index.toFin_ofFin preparation secondIndex)
  let actual ← roots.pairBoundFromFactorsWithStates factorPairs states first.factorIndex second.factorIndex
    first.rootIndex second.rootIndex
  let transport : PairBound roots.candidates
      (Index.fromFactor preparation first.factorIndex first.rootIndex).toFin
      (Index.fromFactor preparation second.factorIndex second.rootIndex).toFin →
      PairBound roots.candidates firstIndex secondIndex := fun retained => by
    rewrite [firstEqual, secondEqual] at retained
    exact retained
  return ⟨transport actual.val, congrArg transport actual.property⟩

/-- Restore the entire original ordered pair table and its summaries through shared root-state readers.

Each actual matrix entry is retained once in the original row-major spine.
The continuation receives equality of the complete default bank, including
all root indices, paid stages, coordinate gaps and cached common summaries.
-/
def pairsWithStates {m : Type → Type} [Monad m] {α : Type} {entries : List PositiveEntry}
    {preparation : Residual.Multiplicity.Family entries} (roots : Family preparation)
    (factorPairs : Basis.Positive.CoprimePairs entries) (states : StateReaders m roots)
    (use : {pairs : Sequence.Selection.Pairs roots.candidates // pairs = roots.pairs factorPairs} → m α) : m α :=
  Sequence.Selection.Pairs.ofFnM (roots.pairBound factorPairs)
    (roots.pairBoundWithStates factorPairs states) use

end Family

end Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity

end
