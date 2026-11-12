module

public import Purelib.RootIsolation.Residual.Multiplicity
public import Purelib.Riemann.RootContinuation.CoherentRoot.Family
public import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
public import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Polynomial.Approximation.Gaussian.Residual
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Coherent roots of retained original multiplicity preparations

Each original factor preparation already owns its exact linear reading or
complete nonlinear isolation. Its coherent realization materializes the same
root programs once. The structural family follows the original retained factor
spine, with dependent lookup preserving that exact factor and isolation.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity

open Purelib
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Polynomial.Dense.Gaussian.Roots.Linear (RootData)
open Purelib.RootIsolation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)

/-- The original prepared factor's bounded root count, retaining its exact linear or stored-isolation parent. -/
@[expose] def count {entry : PositiveEntry} : Residual.Multiplicity.Factor entry → Nat
  | .linear _ _ _ _ => 1
  | .higher _ preparation => preparation.boxes.isolation.tracks.length

/-- Every original positive multiplicity factor retains a positive number of exact or isolated root entries. -/
theorem count_positive {entry : PositiveEntry} (factor : Residual.Multiplicity.Factor entry) : 0 < count factor := by
  cases factor with
  | linear degree data inverseNorm inverseNorm_eq => exact (by decide : (0 : Nat) < 1)
  | higher degree preparation =>
      change 0 < preparation.boxes.isolation.tracks.length
      rewrite [preparation.boxes.isolation.tracks_length]
      exact entry.degreePositive

/-- The first original root index keeps its original factor count and positive bound. -/
@[expose] def firstIndex {entry : PositiveEntry} (factor : Residual.Multiplicity.Factor entry) : Fin (count factor) :=
  ⟨0, count_positive factor⟩

set_option genInjectivity false in
/-- The actual cached root programs of the same retained original multiplicity factor.

Linear data keeps one original exact channel and geometric program with their
same-point readbacks. Nonlinear data keeps one actual coherent certificate per
original stored isolation track; no isolation producer is invoked here.
-/
inductive Realization {entry : PositiveEntry} : Residual.Multiplicity.Factor entry → Type 1 where
  /-- Retain the original exact linear reading's actual channel and geometric cache. -/
  | linear {degree : entry.part.polynomial.natDegree = 1} {data : RootData entry.part.polynomial}
      {inverseNorm : Rational} {inverseNorm_eq : inverseNorm = normSq data.leading⁻¹}
      (value : CoherentNamed) (value_eq : value = CoherentNamed.Coherence.exact data.point)
      (geometric : GeometricApproximation) (geometric_eq : geometric = GeometricApproximation.exact data.point) :
      Realization (.linear degree data inverseNorm inverseNorm_eq)
  /-- Retain the actual coherent root family at the original stored isolation tracks. -/
  | higher {degree : 2 ≤ entry.part.polynomial.natDegree}
      {preparation : RootIsolation.FTA.Squarefree.Preparation ⟨entry.part.squarefree, degree⟩}
      (roots : CoherentRoot.Family preparation.boxes.isolation.tracks) : Realization (.higher degree preparation)

constructive_injectivity Realization

namespace Realization

/-- Build each original prepared factor's numerical root cache once, reusing its exact data or same stored isolation. -/
def ofFactor {entry : PositiveEntry} (factor : Residual.Multiplicity.Factor entry) : Realization factor :=
  match factor with
  | .linear _ data _ _ =>
      let value := CoherentNamed.Coherence.exact data.point
      let geometric := GeometricApproximation.exact data.point
      .linear value rfl geometric rfl
  | .higher _ preparation =>
      .higher (CoherentRoot.Family.ofTracks entry.degreePositive preparation.boxes.isolation.tracks)

/-- Read an original same-index root approximation from its retained exact or nonlinear numerical cache. -/
@[expose] def approximation {entry : PositiveEntry} {factor : Residual.Multiplicity.Factor entry}
    (realization : Realization factor) (index : Fin (count factor)) : Sequence.ApproximationData :=
  match factor, realization with
  | .linear _ _ _ _, .linear _ _ geometric _ => geometric.toApproximation
  | .higher _ _, .higher roots => (roots.get index).approximation

/-- Read the same actual original coherent root channel at its retained factor-root index. -/
@[expose] def channel {entry : PositiveEntry} {factor : Residual.Multiplicity.Factor entry}
    (realization : Realization factor) (index : Fin (count factor)) : CoherentNamed :=
  match factor, realization with
  | .linear _ _ _ _, .linear value _ _ _ => value
  | .higher _ _, .higher roots => (roots.get index).value

/-- The stored original coherent channel agrees with its same retained numerical root approximation. -/
def channel_agrees {entry : PositiveEntry} {factor : Residual.Multiplicity.Factor entry}
    (realization : Realization factor) (index : Fin (count factor)) :
    Equivalence.NamedEquivalent (realization.channel index).name (realization.approximation index).toNamed := by
  cases factor with
  | linear degree data inverseNorm inverseNorm_eq =>
    cases realization with
    | linear value value_eq geometric geometric_eq =>
      change Equivalence.NamedEquivalent value.name geometric.toApproximation.toNamed
      rewrite [value_eq, geometric_eq]
      exact (Sequence.Name.Exact.exact_toConstantNamed data.point).trans
        ((Sequence.Equivalence.approximationEquivalentOfSamplesEq
          (Sequence.Constant.constantApproximation data.point)
          (GeometricApproximation.exact data.point).toApproximation (fun _ => rfl)).toNamed)
  | higher degree preparation =>
    cases realization with
    | higher roots =>
      change Equivalence.NamedEquivalent (roots.get index).value.name (roots.get index).approximation.toNamed
      rewrite [(roots.get index).value_approximation]
      exact Equivalence.NamedEquivalent.refl _

/-- Read quantitative polynomial residual evidence from the same actual original factor-root realization. -/
def residualCertificate {entry : PositiveEntry} {factor : Residual.Multiplicity.Factor entry}
    (roots : Realization factor) (index : Fin (count factor)) :
    Polynomial.Approximation.Gaussian.Residual entry.part.polynomial (roots.channel index) := by
  cases factor with
  | linear degree data inverseNorm inverseNorm_eq =>
    cases roots with
    | linear value value_eq geometric geometric_eq =>
      have equivalent : Equivalence.NamedEquivalent value.name geometric.toApproximation.toNamed := by
        rewrite [value_eq, geometric_eq]
        exact (Sequence.Name.Exact.exact_toConstantNamed data.point).trans
          ((Sequence.Equivalence.approximationEquivalentOfSamplesEq
            (Sequence.Constant.constantApproximation data.point)
            (GeometricApproximation.exact data.point).toApproximation (fun _ => rfl)).toNamed)
      refine ⟨entry.degreePositive, geometric, equivalent, 0, by decide, ?_⟩
      intro stage
      rewrite [geometric_eq]
      change normSq (entry.part.polynomial.eval data.point) ≤
        Purelib.Approximation.Rational.Geometric.Basic.quarterRadius 0 stage
      rewrite [data.root, Purelib.Data.Gaussian.Norm.Basic.normSq_zero]
      exact Purelib.Approximation.Rational.Geometric.Basic.quarterRadius_nonneg (by decide) stage
  | higher degree preparation =>
    cases roots with
    | higher roots => exact (roots.get index).residualCertificate

/-- Read exact scalar provenance from the same retained original linear root entry.

A nonlinear entry stays unclassified even when its selected value is rational.
Its absence supplies no irrationality claim and performs no new root search.
-/
@[expose] def scalar? {entry : PositiveEntry} {factor : Residual.Multiplicity.Factor entry}
    (roots : Realization factor) (index : Fin (count factor)) :
    Option (RationalSidecar (roots.channel index)) := by
  cases factor with
  | linear degree data inverseNorm inverseNorm_eq =>
    cases roots with
    | linear value value_eq geometric geometric_eq =>
      have equivalent : Equivalence.NamedEquivalent value.name (CoherentNamed.Coherence.exact data.point).name := by
        rewrite [value_eq]
        exact Equivalence.NamedEquivalent.refl _
      exact some ⟨data.point, equivalent⟩
  | higher degree preparation =>
    cases roots with
    | higher roots => exact none

/-- Project the actual original nonlinear root certificate at its unchanged factor-root index.

The view retains the original squarefree factor, isolation track and cached
root program. Linear realizations retain their exact scalar reading instead;
this projection never constructs another isolation or coherent root program.
-/
@[expose] def view? {entry : PositiveEntry} {factor : Residual.Multiplicity.Factor entry}
    (roots : Realization factor) (index : Fin (count factor)) :
    Option (CertifiedName.View (roots.channel index)) := by
  cases factor with
  | linear degree data inverseNorm inverseNorm_eq =>
    cases roots with
    | linear value value_eq geometric geometric_eq => exact none
  | higher degree preparation =>
    cases roots with
    | higher roots =>
      exact some (CertifiedName.View.ofRoot (roots.get index) ⟨entry.part.squarefree, entry.degreePositive⟩)

end Realization

set_option genInjectivity false in
/-- The structural coherent-root cache of the original retained factor-preparation family. -/
inductive Family : {entries : List PositiveEntry} → Residual.Multiplicity.Family entries → Type 1 where
  /-- The original empty preparation has no realized roots. -/
  | nil : Family Residual.Multiplicity.Family.nil
  /-- Retain the original head realization and original dependent tail cache. -/
  | cons {head : PositiveEntry} {tail : List PositiveEntry}
      {factor : Residual.Multiplicity.Factor head} {remaining : Residual.Multiplicity.Family tail}
      (roots : Realization factor) (tailRoots : Family remaining) : Family (.cons factor remaining)

constructive_injectivity Family

namespace Family

/-- Realize every original stored factor preparation once without another decomposition or isolation. -/
def ofPreparation : {entries : List PositiveEntry} → (preparation : Residual.Multiplicity.Family entries) →
    Family preparation
  | [], .nil => .nil
  | _ :: _, .cons head tail => .cons (Realization.ofFactor head) (ofPreparation tail)

/-- Read the actual original root realization at the same retained bounded factor-list index. -/
@[expose] def get : {entries : List PositiveEntry} → {preparation : Residual.Multiplicity.Family entries} →
    Family preparation → (index : Fin entries.length) → Realization (preparation.get index)
  | [], .nil, .nil, index => Fin.elim0 index
  | _ :: _, .cons _ _, .cons head _, ⟨0, _⟩ => head
  | _ :: _, .cons _ _, .cons _ tail, ⟨index + 1, bound⟩ =>
      get tail ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- Zero lookup consumes the stored original head realization. -/
theorem get_head {head : PositiveEntry} {tail : List PositiveEntry}
    {factor : Residual.Multiplicity.Factor head} {remaining : Residual.Multiplicity.Family tail}
    (roots : Realization factor) (tailRoots : Family remaining) : (Family.cons roots tailRoots).get 0 = roots := rfl

/-- Successor lookup consumes the stored original tail and unchanged predecessor factor index. -/
theorem get_tail {head : PositiveEntry} {tail : List PositiveEntry}
    {factor : Residual.Multiplicity.Factor head} {remaining : Residual.Multiplicity.Family tail}
    (roots : Realization factor) (tailRoots : Family remaining) (index : Fin tail.length) :
    (Family.cons roots tailRoots).get index.succ = tailRoots.get index := rfl

end Family

end Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity

end
