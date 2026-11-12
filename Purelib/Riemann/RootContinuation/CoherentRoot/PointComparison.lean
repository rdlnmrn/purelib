module

public import Purelib.Riemann.RootContinuation.CoherentRoot.PointSeparation
public import Purelib.Riemann.RootContinuation.CoherentRoot.Refinement
public import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.RootCofactor.Bounds
public import Purelib.RootIsolation.FTA.Positive.Input
public import Purelib.Approximation.Gaussian.Division.Prepared.Decision
public import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
public import Purelib.Polynomial.Dense.Gaussian.Roots.Candidates
import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Arithmetic.Exact
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Approximation.Gaussian.Equivalence.Sampling
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original squarefree root comparison with an exact Gaussian point

Exact coefficient evaluation distinguishes nonroots. At a displayed root,
the original linear division and squarefree cofactor compute a sufficient
neighborhood request. The actual original cache box then certifies equality
or positive point separation, without an additional successful-search bound.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Geometry.Rational
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Polynomial.Dense.Gaussian.Roots.Certificate (ExactRoot)

namespace CertifiedName

/-- A sufficiently refined original box containing a displayed squarefree root agrees with that exact point.

The same retained cofactor's positive lower bound controls the original
polynomial residual at every later cached sample. Division by that bound
gives a geometric displacement bound after the paid original stage; the
finite tail comparison computes its own indices at every caller tolerance.
-/
def compare_point_of_cofactor {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (point : Canonical) {start : Nat}
    (cofactor : Squarefree.RootCofactor polynomial point) (refinement : Refinement root start)
    (budget : refinement.targetSq = cofactor.radius ambient ^ 2) (inside : refinement.current.box.Contains point) :
    Equivalence.Equivalent root.approximation (Sequence.Constant.constantApproximation point) := by
  let margin := cofactor.margin
  have marginPositive : 0 < margin := cofactor.margin_pos
  let scale := residualScale polynomial ambient track / margin
  have scaleNonnegative : 0 ≤ scale := Fraction.Order.Field.div_nonneg_direct
    (residualScale_nonneg polynomial ambient track) marginPositive.le
  have samples : ∀ index, refinement.index ≤ index → normSq (root.approximation.sample index - point) ≤
      Geometric.Basic.quarterRadius scale index := by
    intro index order
    have sampleInside := refinement.sample_inside order
    have close := refinement.current.box.normSq_sub_le_diagonalSq sampleInside inside
    have diagonal := refinement.diagonal_lt
    rewrite [budget] at diagonal
    have lower := cofactor.normSq_eval_lower (refinement.current.refinesAmbient.contains inside)
      (root.sample_inside index) (close.trans diagonal.le)
    have multiplied := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lower
      (Purelib.Data.Gaussian.Norm.Basic.normSq_nonneg (root.approximation.sample index - point))
    have identity := Dense.Gaussian.Factorization.Identity.eval_factorization cofactor.factorization
      (root.approximation.sample index)
    rewrite [Dense.Gaussian.Linear.Translated.translatedCoordinate_eval] at identity
    rewrite [← Purelib.Data.Gaussian.Norm.Basic.normSq_mul, ← identity] at multiplied
    have divided := (Fraction.Order.Field.le_div_iff_pos marginPositive).mpr multiplied
    have residual := root.residual index
    rewrite [← root.approximation_eq] at residual
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct residual
      (Fraction.Order.Field.inv_pos_direct marginPositive).le
    change normSq (polynomial.eval (root.approximation.sample index)) / margin ≤ _ at scaled
    have same : Geometric.Basic.quarterRadius (residualScale polynomial ambient track) index / margin =
        Geometric.Basic.quarterRadius scale index := by
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
      change ((residualScale polynomial ambient track * (1 / 4) ^ index) * margin⁻¹) =
        (residualScale polynomial ambient track * margin⁻¹) * (1 / 4) ^ index
      exact (Fraction.Field.mul_assoc _ _ _).trans
        ((congrArg (fun value => residualScale polynomial ambient track * value) (Fraction.Field.mul_comm _ _)).trans
          (Fraction.Field.mul_assoc _ _ _).symm)
    exact divided.trans (scaled.trans_eq same)
  exact Sequence.Equivalence.equivalent_constant_after root.approximation point refinement.index
    scale scaleNonnegative samples

/-- Transport the actual cofactor approximation comparison to the same original coherent channels.

The original root, paid refinement, cofactor and exact point remain the inputs.
Only the existing approximation-to-name adapters are added to the retained
finite comparison; no second refinement or neighborhood search is performed.
-/
def equivalent_point_of_cofactor {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (point : Canonical) {start : Nat}
    (cofactor : Squarefree.RootCofactor polynomial point) (refinement : Refinement root start)
    (budget : refinement.targetSq = cofactor.radius ambient ^ 2) (inside : refinement.current.box.Contains point) :
    Equivalence.NamedEquivalent root.value.name (CoherentNamed.Coherence.exact point).name := by
  rewrite [root.value_approximation]
  exact (root.compare_point_of_cofactor point cofactor refinement budget inside).toNamed.trans
    (Sequence.Name.Exact.exact_toConstantNamed point).symm

end CertifiedName

set_option genInjectivity false in
/-- Exact original-channel agreement or positive separation at one original paid root state. -/
inductive PointOutcome {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {root : CertifiedName track} {start : Nat}
    (refinement : Refinement root start) (point : Canonical) : Type 1 where
  /-- The original numerical root channel agrees with this displayed exact point. -/
  | equal (equivalent : Equivalence.NamedEquivalent root.value.name (CoherentNamed.Coherence.exact point).name)
  /-- The actual original paid-state box has a displayed positive coordinate gap from this point. -/
  | distinct (separation : Box.SeparationCertificate refinement.current.box (Box.Point.pointBox point))

constructive_injectivity PointOutcome

set_option genInjectivity false in
/-- A complete coefficient-computed comparison of an original squarefree root channel with an exact point.

Nonroots retain their original evaluation and exclusion request. Displayed
roots retain the original division/cofactor, paid request and actual cache box.
The original channels and starts index both possible operational outcomes.
-/
inductive PointComparison {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (point : Canonical) (start : Nat) :
    Type 1 where
  /-- The point is an original polynomial nonroot, with its computed original-stage separation. -/
  | nonroot (separation : PointSeparation root point start)
  /-- A displayed source root retains its same squarefree cofactor and original paid-stage outcome. -/
  | root (cofactor : Squarefree.RootCofactor polynomial point) (refinement : Refinement root start)
      (budget : refinement.targetSq = cofactor.radius ambient ^ 2) (outcome : PointOutcome refinement point)

constructive_injectivity PointComparison

namespace PointComparison

/-- Compute point agreement or sample separation from the original squarefree coefficient and track data. -/
@[expose] def prepare {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (input : FTA.Positive.Input.PositiveInput polynomial) (point : Canonical) (start : Nat) :
    PointComparison root point start :=
  let value := polynomial.eval point
  if zero : value = 0 then
    let cofactor := Squarefree.RootCofactor.ofRoot polynomial point input.nonzero input.squarefree zero
    let request := cofactor.radius ambient ^ 2
    let refinement := Refinement.ofTarget root start request
      (Fraction.Order.Arithmetic.pow_pos_direct (cofactor.radius_pos ambient) 2)
    have budget : refinement.targetSq = cofactor.radius ambient ^ 2 :=
      Refinement.ofTarget_targetSq root start request _
    if inside : refinement.current.box.Contains point then
      .root cofactor refinement budget
        (.equal (root.equivalent_point_of_cofactor point cofactor refinement budget inside))
    else
      .root cofactor refinement budget (.distinct
        (Box.Point.separationCertificateOfNotContains refinement.current.box point inside))
  else
    .nonroot (PointSeparation.ofValue root point value rfl zero start)

/-- Read an exact scalar only from this actual original point comparison's checked equality outcome.

The original cofactor, paid refinement and failure outcomes remain in the
supplied comparison. No polynomial equation or box containment alone supplies
the numerical-channel identity returned by this projection.
-/
@[expose] def scalar? {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {root : CertifiedName track} {point : Canonical} {start : Nat}
    (comparison : PointComparison root point start) : Option (RationalSidecar root.value) :=
  match comparison with
  | .nonroot _ => none
  | .root _ _ _ outcome => match outcome with
      | .equal equivalent => some ⟨point, equivalent⟩
      | .distinct _ => none

/-- A retained equality projects its same point and actual original-channel relation. -/
theorem scalar?_equal {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {root : CertifiedName track} {point : Canonical} {start : Nat}
    (cofactor : Squarefree.RootCofactor polynomial point) (refinement : Refinement root start)
    (budget : refinement.targetSq = cofactor.radius ambient ^ 2)
    (equivalent : Equivalence.NamedEquivalent root.value.name (CoherentNamed.Coherence.exact point).name) :
    (PointComparison.root cofactor refinement budget (.equal equivalent)).scalar? =
      some ⟨point, equivalent⟩ := rfl

/-- A checked distinct coefficient root retains no exact reading of the selected original root. -/
theorem scalar?_distinct {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {root : CertifiedName track} {point : Canonical} {start : Nat}
    (cofactor : Squarefree.RootCofactor polynomial point) (refinement : Refinement root start)
    (budget : refinement.targetSq = cofactor.radius ambient ^ 2)
    (separation : Box.SeparationCertificate refinement.current.box (Box.Point.pointBox point)) :
    (PointComparison.root cofactor refinement budget (.distinct separation)).scalar? = none := rfl

/-- Prepare the original shifted root channel or certify its exact zero at the same retained comparison. -/
def differenceDecision {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {root : CertifiedName track} {point : Canonical} {start : Nat}
    (comparison : PointComparison root point start) :
    Division.Prepared.Decision (CoherentNamed.add root.value (CoherentNamed.Coherence.exact (-point))) := by
  cases comparison with
  | nonroot separation => exact .prepared separation.prepareDifference
  | root _ refinement _ outcome =>
      cases outcome with
      | distinct separation =>
          have samples : ∀ later, refinement.index ≤ later → separation.gap ^ 2 ≤
              normSq (root.approximation.sample later - point) := by
            intro later order
            exact separation.lower (refinement.sample_inside order) (Box.Point.pointBox_contains point)
          rewrite [root.value_approximation]
          exact .prepared (root.approximation.prepareDifference point refinement.index (separation.gap ^ 2)
            (Fraction.Order.Arithmetic.pow_pos_direct separation.positive 2) samples)
      | equal equivalent =>
          let exactPoint := CoherentNamed.Coherence.exact point
          let negative := CoherentNamed.Coherence.exact (-point)
          have respects := Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
            root.value exactPoint negative negative equivalent (Equivalence.NamedEquivalent.refl _)
          have constant := Arithmetic.Exact.exactAdd_named_equivalent point (-point)
          have cancel : point + -point = 0 :=
            (Purelib.Data.Gaussian.Basic.add_comm _ _).trans
              (Purelib.Data.Gaussian.Basic.Canonical.neg_add_cancel point)
          rewrite [cancel] at constant
          exact .excluded (respects.trans constant)

/-- Decide exact zero or a prepared presentation of the same original squarefree root channel.

The displayed-point comparison at zero computes all required refinement and
separation. The original addition-by-zero comparison transports its result
back to the unchanged original root channel.
-/
def decide {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (input : FTA.Positive.Input.PositiveInput polynomial) (start : Nat) : Division.Prepared.Decision root.value := by
  let comparison := prepare root input 0 start
  have shifted : Equivalence.NamedEquivalent
      (CoherentNamed.add root.value (CoherentNamed.Coherence.exact (-0))).name root.value.name := by
    rewrite [show -(0 : Canonical) = 0 by decide +kernel]
    exact Arithmetic.Add.addRightZero root.value (CoherentNamed.Coherence.exact 0) (Equivalence.NamedEquivalent.refl _)
  cases comparison.differenceDecision with
  | prepared prepared => exact .prepared (prepared.transport shifted)
  | excluded zero => exact .excluded (shifted.symm.trans zero)

end PointComparison

namespace CertifiedName.View

/-- Original candidate comparisons, their unvisited suffix and an optional checked original-channel reading.

The dependent entries retain every exact candidate and actual point comparison
in its original order. The reading, when present, is linked to this same
supplied View channel; no root owner is replaced by the exact point.
-/
abbrev CandidateResult {channel : CoherentNamed} (view : CertifiedName.View channel) (start : Nat) : Type 1 :=
  List (Σ candidate : ExactRoot view.polynomial, PointComparison view.root candidate.point start) ×
    List (ExactRoot view.polynomial) × Option (RationalSidecar channel)

/-- Inspect an ordered exact candidate bank against the same original root and retain every actual paid attempt.

Each demanded candidate executes the original point comparison once. A checked
equality stores the transported original-channel reading and unvisited suffix;
rejection retains the actual typed comparison before inspecting the tail.
-/
@[expose] def inspectCandidates {channel : CoherentNamed} (view : CertifiedName.View channel) (start : Nat) :
    (candidates : List (ExactRoot view.polynomial)) → CandidateResult view start
  | [] => ⟨[], [], none⟩
  | candidate :: tail =>
      let comparison := PointComparison.prepare view.root view.input candidate.point start
      let entry : Σ candidate : ExactRoot view.polynomial, PointComparison view.root candidate.point start :=
        ⟨candidate, comparison⟩
      match comparison.scalar? with
      | some reading => ⟨[entry], tail, some ⟨reading.value, view.equivalent.trans reading.equivalent⟩⟩
      | none =>
          let remaining := inspectCandidates view start tail
          ⟨entry :: remaining.1, remaining.2⟩

/-- The empty candidate bank retains an empty attempt list, empty suffix and no exact reading. -/
theorem inspectCandidates_nil {channel : CoherentNamed} (view : CertifiedName.View channel) (start : Nat) :
    view.inspectCandidates start [] = ⟨[], [], none⟩ := rfl

/-- One candidate retains the original point comparison and shares its actual equality test with the retained result. -/
theorem inspectCandidates_cons {channel : CoherentNamed} (view : CertifiedName.View channel) (start : Nat)
    (candidate : ExactRoot view.polynomial) (tail : List (ExactRoot view.polynomial)) :
    view.inspectCandidates start (candidate :: tail) =
      (let comparison := PointComparison.prepare view.root view.input candidate.point start
       let entry : Σ candidate : ExactRoot view.polynomial, PointComparison view.root candidate.point start :=
         ⟨candidate, comparison⟩
       match comparison.scalar? with
       | some reading => ⟨[entry], tail, some ⟨reading.value, view.equivalent.trans reading.equivalent⟩⟩
       | none =>
           let remaining := view.inspectCandidates start tail
           ⟨entry :: remaining.1, remaining.2⟩) := rfl

/-- Attempted candidates followed by the unvisited suffix preserve the complete original bank and duplicate order. -/
theorem inspectCandidates_partition {channel : CoherentNamed} (view : CertifiedName.View channel) (start : Nat)
    (candidates : List (ExactRoot view.polynomial)) :
    ((view.inspectCandidates start candidates).1.map fun entry => entry.1) ++
      (view.inspectCandidates start candidates).2.1 = candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate tail previous =>
      rewrite [inspectCandidates_cons]
      dsimp only
      cases (PointComparison.prepare view.root view.input candidate.point start).scalar? with
      | some value => rfl
      | none =>
          change candidate :: (((view.inspectCandidates start tail).1.map fun entry => entry.1) ++
            (view.inspectCandidates start tail).2.1) = candidate :: tail
          exact congrArg (List.cons candidate) previous

end CertifiedName.View

end Purelib.Riemann.RootContinuation.CoherentRoot

end
