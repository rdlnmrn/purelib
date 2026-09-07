import mathlib.Tactic.QuotientFreeRing
import RFAP.Cauchy.ProductSigns
import RFAP.Sturm.IntervalSign

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

namespace RFAP.CauchyCells

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Interval := RFAP.PathClearance.Interval

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.Sturm
open RFAP.PathClearance
open RFAP.IntervalSign
open RFAP.CauchyProductSigns

/-- A proof-relevant finite list of whole-cell strict-sign certificates. -/
inductive ChainSignCertificates (interval : Interval) :
    List Polynomial → Type
  | nil : ChainSignCertificates interval []
  | cons {p : Polynomial} {chain : List Polynomial}
      (head : Certificate p interval)
      (tail : ChainSignCertificates interval chain) :
      ChainSignCertificates interval (p :: chain)

namespace ChainSignCertificates

theorem endpoint_signs {interval : Interval} {chain : List Polynomial}
    (certificates : ChainSignCertificates interval chain) :
    List.Forall₂ (fun x y => sign x = sign y)
      (chain.map fun p => p.eval interval.lower)
      (chain.map fun p => p.eval interval.upper) := by
  induction certificates with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      apply List.Forall₂.cons
      · exact sign_eq_of_mul_pos head.endpoint_stable
      · exact inductionHypothesis

theorem endpointVariation_eq {interval : Interval} {chain : List Polynomial}
    (certificates : ChainSignCertificates interval chain) :
    endpointVariation2 chain interval.lower =
      endpointVariation2 chain interval.upper := by
  apply variation2_congr_of_forall₂_sign
  exact certificates.endpoint_signs

/-- Whole-cell strict signs for the actual raw signed chain force its doubled
Cauchy index to vanish. -/
theorem cauchyIndex2_eq_zero {R S : Polynomial} {interval : Interval}
    (certificates : ChainSignCertificates interval
      (signedRemainderChain S R)) :
    cauchyIndex2 R S interval.lower interval.upper = 0 := by
  unfold cauchyIndex2
  rw [certificates.endpointVariation_eq]
  exact Int.sub_self _

end ChainSignCertificates

def chainSignCertificates? (interval : Interval) :
    (chain : List Polynomial) → Option (ChainSignCertificates interval chain)
  | [] => some .nil
  | p :: chain =>
      match RFAP.IntervalSign.certificate? p interval with
      | none => none
      | some head =>
          match chainSignCertificates? interval chain with
          | none => none
          | some tail => some (.cons head tail)

/-- One locally resolved signed Euclidean step.  Both outer chain members
have fixed signs, while their displayed common sample has opposite signs. -/
structure SignedStepCellCertificate
    (p q : Polynomial) (interval : Interval) where
  sample : Coordinate
  sampleInside : interval.Contains sample
  leftMargin : denseEvalSqLipschitzBound p interval *
      sampleRadiusSq interval sample < p.eval sample ^ 2
  rightMargin :
    denseEvalSqLipschitzBound (-((divMod p q).remainder)) interval *
        sampleRadiusSq interval sample <
      (-((divMod p q).remainder)).eval sample ^ 2
  outerOpposite :
    p.eval sample * (-((divMod p q).remainder)).eval sample < 0

namespace SignedStepCellCertificate

def leftCertificate {p q : Polynomial} {interval : Interval}
    (certificate : SignedStepCellCertificate p q interval) :
    Certificate p interval where
  sample := certificate.sample
  sampleInside := certificate.sampleInside
  margin := certificate.leftMargin

def rightCertificate {p q : Polynomial} {interval : Interval}
    (certificate : SignedStepCellCertificate p q interval) :
    Certificate (-((divMod p q).remainder)) interval where
  sample := certificate.sample
  sampleInside := certificate.sampleInside
  margin := certificate.rightMargin

theorem outer_mul_neg {p q : Polynomial} {interval : Interval}
    (certificate : SignedStepCellCertificate p q interval)
    {t : Coordinate} (inside : interval.Contains t) :
    p.eval t * (-((divMod p q).remainder)).eval t < 0 := by
  have leftStable := certificate.leftCertificate.eval_mul_sample_pos inside
  have rightStable := certificate.rightCertificate.eval_mul_sample_pos inside
  change 0 < p.eval t * p.eval certificate.sample at leftStable
  change 0 < (-((divMod p q).remainder)).eval t *
    (-((divMod p q).remainder)).eval certificate.sample at rightStable
  apply sign_eq_neg_one_iff.mp
  rw [sign_mul, sign_eq_of_mul_pos leftStable,
    sign_eq_of_mul_pos rightStable, ← sign_mul,
    sign_of_neg certificate.outerOpposite]

theorem local_jump_sum {p q : Polynomial} {interval : Interval}
    (certificate : SignedStepCellCertificate p q interval)
    {t : Coordinate} (inside : interval.Contains t) :
    signJump (p.eval t) (q.eval t) +
        signJump (q.eval t) ((-((divMod p q).remainder)).eval t) = 2 :=
  signJump_add_signJump_of_outer_mul_neg
    (certificate.outer_mul_neg inside)

theorem endpoint_cancellation {p q : Polynomial} {interval : Interval}
    (certificate : SignedStepCellCertificate p q interval) :
    signJump (p.eval interval.lower) (q.eval interval.lower) +
        signJump (q.eval interval.lower)
          ((-((divMod p q).remainder)).eval interval.lower) =
      signJump (p.eval interval.upper) (q.eval interval.upper) +
        signJump (q.eval interval.upper)
          ((-((divMod p q).remainder)).eval interval.upper) := by
  rw [certificate.local_jump_sum ⟨le_rfl, interval.valid⟩,
    certificate.local_jump_sum ⟨interval.valid, le_rfl⟩]

end SignedStepCellCertificate

/-- Executable classifier for one cancelling signed Euclidean triple, using
the displayed left endpoint as its common finite sample. -/
def signedStepCellCertificate?
    (p q : Polynomial) (interval : Interval) :
    Option (SignedStepCellCertificate p q interval) :=
  let sample := interval.lower
  let next := -((divMod p q).remainder)
  if leftMargin : denseEvalSqLipschitzBound p interval *
      sampleRadiusSq interval sample < p.eval sample ^ 2 then
    if rightMargin : denseEvalSqLipschitzBound next interval *
        sampleRadiusSq interval sample < next.eval sample ^ 2 then
      if outerOpposite : p.eval sample * next.eval sample < 0 then
        some
          { sample := sample
            sampleInside := ⟨le_rfl, interval.valid⟩
            leftMargin := leftMargin
            rightMargin := rightMargin
            outerOpposite := outerOpposite }
      else none
    else none
  else none

/-- A nonempty chain whose fixed-sign heads and disjoint signed triples all
cancel between the two endpoints. -/
inductive NeutralChainCertificate (interval : Interval) :
    (head : Polynomial) → (tail : List Polynomial) → Type
  | single {p : Polynomial}
      (headStable : Certificate p interval) :
      NeutralChainCertificate interval p []
  | stable {p q : Polynomial} {tail : List Polynomial}
      (headStable : Certificate p interval)
      (rest : NeutralChainCertificate interval q tail) :
      NeutralChainCertificate interval p (q :: tail)
  | event {p q r : Polynomial} {tail : List Polynomial}
      (nextEq : r = -((divMod p q).remainder))
      (step : SignedStepCellCertificate p q interval)
      (rest : NeutralChainCertificate interval r tail) :
      NeutralChainCertificate interval p (q :: r :: tail)

namespace NeutralChainCertificate

def headStable {interval : Interval} {p : Polynomial}
    {tail : List Polynomial}
    (certificate : NeutralChainCertificate interval p tail) :
    Certificate p interval :=
  match certificate with
  | .single headCertificate => headCertificate
  | .stable headCertificate .. => headCertificate
  | .event _ step .. => step.leftCertificate

theorem headEndpointSign_eq {interval : Interval} {p : Polynomial}
    {tail : List Polynomial}
    (certificate : NeutralChainCertificate interval p tail) :
    sign (p.eval interval.lower) = sign (p.eval interval.upper) :=
  sign_eq_of_mul_pos certificate.headStable.endpoint_stable

theorem endpointVariation_eq {interval : Interval} {p : Polynomial}
    {tail : List Polynomial}
    (certificate : NeutralChainCertificate interval p tail) :
    endpointVariation2 (p :: tail) interval.lower =
      endpointVariation2 (p :: tail) interval.upper := by
  induction certificate with
  | single => rfl
  | @stable p q tail headStable rest inductionHypothesis =>
      have headSign := sign_eq_of_mul_pos headStable.endpoint_stable
      have nextSign := rest.headEndpointSign_eq
      change signJump (p.eval interval.lower) (q.eval interval.lower) +
          endpointVariation2 (q :: tail) interval.lower =
        signJump (p.eval interval.upper) (q.eval interval.upper) +
          endpointVariation2 (q :: tail) interval.upper
      rw [signJump_congr headSign nextSign, inductionHypothesis]
  | @event p q r tail nextEq step rest inductionHypothesis =>
      subst r
      have localCancellation := step.endpoint_cancellation
      change
        signJump (p.eval interval.lower) (q.eval interval.lower) +
            (signJump (q.eval interval.lower)
                ((-((divMod p q).remainder)).eval interval.lower) +
              endpointVariation2
                ((-((divMod p q).remainder)) :: tail) interval.lower) =
          signJump (p.eval interval.upper) (q.eval interval.upper) +
            (signJump (q.eval interval.upper)
                ((-((divMod p q).remainder)).eval interval.upper) +
              endpointVariation2
                ((-((divMod p q).remainder)) :: tail) interval.upper)
      rw [← Nat.add_assoc, ← Nat.add_assoc, localCancellation,
        inductionHypothesis]

end NeutralChainCertificate

/-- Structural finite scanner for an arbitrary number of disjoint cancelling
events in one signed chain. -/
def neutralChainCertificate? (interval : Interval) (head : Polynomial) :
    (tail : List Polynomial) →
      Option (NeutralChainCertificate interval head tail)
  | [] =>
      match RFAP.IntervalSign.certificate? head interval with
      | none => none
      | some headStable => some (.single headStable)
  | q :: tail =>
      match RFAP.IntervalSign.certificate? head interval with
      | none => none
      | some headStable =>
          match tail with
          | [] =>
              match RFAP.IntervalSign.certificate? q interval with
              | none => none
              | some qStable => some (.stable headStable (.single qStable))
          | r :: suffix =>
              match RFAP.IntervalSign.certificate? q interval with
              | some _ =>
                  match neutralChainCertificate? interval q (r :: suffix) with
                  | none => none
                  | some rest => some (.stable headStable rest)
              | none =>
                  if nextEq : r = -((divMod head q).remainder) then
                    match signedStepCellCertificate? head q interval with
                    | none => none
                    | some step =>
                        match neutralChainCertificate? interval r suffix with
                        | none => none
                        | some rest => some (.event nextEq step rest)
                  else none

inductive NeutralChainCertificates (interval : Interval) :
    List Polynomial → Type
  | nil : NeutralChainCertificates interval []
  | cons {head : Polynomial} {tail : List Polynomial}
      (certificate : NeutralChainCertificate interval head tail) :
      NeutralChainCertificates interval (head :: tail)

namespace NeutralChainCertificates

theorem endpointVariation_eq {interval : Interval} {chain : List Polynomial}
    (certificates : NeutralChainCertificates interval chain) :
    endpointVariation2 chain interval.lower =
      endpointVariation2 chain interval.upper := by
  cases certificates with
  | nil => rfl
  | cons certificate => exact certificate.endpointVariation_eq

theorem cauchyIndex2_eq_zero {R S : Polynomial} {interval : Interval}
    (certificates : NeutralChainCertificates interval
      (signedRemainderChain S R)) :
    cauchyIndex2 R S interval.lower interval.upper = 0 := by
  unfold cauchyIndex2
  rw [certificates.endpointVariation_eq]
  exact Int.sub_self _

end NeutralChainCertificates

def neutralChainCertificates? (interval : Interval) :
    (chain : List Polynomial) → Option (NeutralChainCertificates interval chain)
  | [] => some .nil
  | head :: tail =>
      match neutralChainCertificate? interval head tail with
      | none => none
      | some certificate => some (.cons certificate)

/-- Executable neutral-cell check for the exact raw Cauchy chain. -/
def neutralCauchyCell?
    (R S : Polynomial) (interval : Interval) : Bool :=
  (neutralChainCertificates? interval (signedRemainderChain S R)).isSome

theorem cauchyIndex2_eq_zero_of_neutralCauchyCell
    (R S : Polynomial) (interval : Interval)
    (checked : neutralCauchyCell? R S interval = true) :
    cauchyIndex2 R S interval.lower interval.upper = 0 := by
  unfold neutralCauchyCell? at checked
  cases found : neutralChainCertificates? interval
      (signedRemainderChain S R) with
  | none => simp [found] at checked
  | some certificates =>
      exact NeutralChainCertificates.cauchyIndex2_eq_zero certificates

/-- If the recursively emitted tail is neutral, the complete Cauchy index is
exactly the change of the first two signed-chain jumps. -/
theorem cauchyIndex2_eq_firstJumps_of_neutralTail
    {R S : Polynomial} {interval : Interval}
    (RNonzero : R.isZero = false)
    (tail : NeutralChainCertificates interval
      (signedRemainderChain R (-((divMod S R).remainder)))) :
    cauchyIndex2 R S interval.lower interval.upper =
      (signJump (S.eval interval.lower) (R.eval interval.lower) : Int) -
        signJump (S.eval interval.upper) (R.eval interval.upper) := by
  unfold cauchyIndex2
  rw [endpointVariation2_signedRemainderChain_step S R RNonzero,
    endpointVariation2_signedRemainderChain_step S R RNonzero,
    tail.endpointVariation_eq]
  simp only [Nat.cast_add]
  ring1

/-- Formal finite center signs for one actual Cauchy pair, together with the
exact event index represented between the two displayed rational endpoints. -/
structure CauchyEventSigns
    (R S : Polynomial) (interval : Interval) where
  numerator : FiniteSign
  denominator : FiniteSign
  nonzero : numerator ≠ .zero ∨ denominator ≠ .zero
  numeratorLowerStable : FiniteSign.Stable numerator
    (FiniteSign.ofCoordinate (R.eval interval.lower))
  denominatorLowerStable : FiniteSign.Stable denominator
    (FiniteSign.ofCoordinate (S.eval interval.lower))
  numeratorUpperStable : FiniteSign.Stable numerator
    (FiniteSign.ofCoordinate (R.eval interval.upper))
  denominatorUpperStable : FiniteSign.Stable denominator
    (FiniteSign.ofCoordinate (S.eval interval.upper))
  index : cauchyIndex2 R S interval.lower interval.upper =
    FiniteSign.eventIndex2 numerator denominator
      (FiniteSign.ofCoordinate (R.eval interval.lower))
      (FiniteSign.ofCoordinate (S.eval interval.lower))
      (FiniteSign.ofCoordinate (R.eval interval.upper))
      (FiniteSign.ofCoordinate (S.eval interval.upper))

namespace CauchyEventSigns

/-- A neutral full chain with a fixed denominator sign is the zero-event
branch.  The formal numerator is deliberately left unknown. -/
def ofNeutral
    {R S : Polynomial} {interval : Interval}
    (denominator : Certificate S interval)
    (chain : NeutralChainCertificates interval
      (signedRemainderChain S R)) :
    CauchyEventSigns R S interval := by
  let denominatorSign := FiniteSign.ofCoordinate (S.eval interval.lower)
  have denominatorNonzero : denominatorSign ≠ .zero := by
    simpa only [denominatorSign, FiniteSign.ofCoordinate_ne_zero_iff] using
      denominator.eval_ne_zero ⟨le_rfl, interval.valid⟩
  have denominatorStable : denominatorSign =
      FiniteSign.ofCoordinate (S.eval interval.upper) := by
    apply FiniteSign.value_injective
    simp only [denominatorSign, FiniteSign.value_ofCoordinate]
    exact sign_eq_of_mul_pos denominator.endpoint_stable
  refine
    { numerator := .zero
      denominator := denominatorSign
      nonzero := Or.inr denominatorNonzero
      numeratorLowerStable := Or.inl rfl
      denominatorLowerStable := Or.inr rfl
      numeratorUpperStable := Or.inl rfl
      denominatorUpperStable := Or.inr denominatorStable
      index := ?_ }
  rw [chain.cauchyIndex2_eq_zero]
  simp only [FiniteSign.eventIndex2, FiniteSign.leftEndpointIndex2,
    denominatorNonzero, ↓reduceIte, sub_self]

/-- A fixed nonzero numerator and neutral recursive tail represent the sole
possibly nonzero first-chain event; no root parameter is introduced. -/
def ofResolvedNumerator
    {R S : Polynomial} {interval : Interval}
    (numerator : Certificate R interval)
    (tail : NeutralChainCertificates interval
      (signedRemainderChain R (-((divMod S R).remainder)))) :
    CauchyEventSigns R S interval := by
  let numeratorSign := FiniteSign.ofCoordinate (R.eval interval.lower)
  have numeratorNonzero : numeratorSign ≠ .zero := by
    simpa only [numeratorSign, FiniteSign.ofCoordinate_ne_zero_iff] using
      numerator.eval_ne_zero ⟨le_rfl, interval.valid⟩
  have numeratorStable : numeratorSign =
      FiniteSign.ofCoordinate (R.eval interval.upper) := by
    apply FiniteSign.value_injective
    simp only [numeratorSign, FiniteSign.value_ofCoordinate]
    exact sign_eq_of_mul_pos numerator.endpoint_stable
  refine
    { numerator := numeratorSign
      denominator := .zero
      nonzero := Or.inl numeratorNonzero
      numeratorLowerStable := Or.inr rfl
      denominatorLowerStable := Or.inl rfl
      numeratorUpperStable := Or.inr numeratorStable
      denominatorUpperStable := Or.inl rfl
      index := ?_ }
  rw [cauchyIndex2_eq_firstJumps_of_neutralTail
    numerator.polynomial_nonzero tail,
    ← FiniteSign.jump_ofCoordinate,
    ← FiniteSign.jump_ofCoordinate, ← numeratorStable]
  exact (FiniteSign.eventIndex2_of_stableNumerator
    numeratorSign
    (FiniteSign.ofCoordinate (S.eval interval.lower))
    (FiniteSign.ofCoordinate (S.eval interval.upper))
    numeratorNonzero).symm

/-- Replace the formal center by any other nonzero finite pair stable against
the same two endpoint pairs. -/
def recenter
    {R S : Polynomial} {interval : Interval}
    (data : CauchyEventSigns R S interval)
    (numerator denominator : FiniteSign)
    (nonzero : numerator ≠ .zero ∨ denominator ≠ .zero)
    (numeratorLowerStable : FiniteSign.Stable numerator
      (FiniteSign.ofCoordinate (R.eval interval.lower)))
    (denominatorLowerStable : FiniteSign.Stable denominator
      (FiniteSign.ofCoordinate (S.eval interval.lower)))
    (numeratorUpperStable : FiniteSign.Stable numerator
      (FiniteSign.ofCoordinate (R.eval interval.upper)))
    (denominatorUpperStable : FiniteSign.Stable denominator
      (FiniteSign.ofCoordinate (S.eval interval.upper))) :
    CauchyEventSigns R S interval where
  numerator := numerator
  denominator := denominator
  nonzero := nonzero
  numeratorLowerStable := numeratorLowerStable
  denominatorLowerStable := denominatorLowerStable
  numeratorUpperStable := numeratorUpperStable
  denominatorUpperStable := denominatorUpperStable
  index := by
    rw [data.index]
    exact FiniteSign.eventIndex2_eq_of_stable
      data.numerator data.denominator numerator denominator
      (FiniteSign.ofCoordinate (R.eval interval.lower))
      (FiniteSign.ofCoordinate (S.eval interval.lower))
      (FiniteSign.ofCoordinate (R.eval interval.upper))
      (FiniteSign.ofCoordinate (S.eval interval.upper))
      ⟨data.nonzero, data.numeratorLowerStable,
        data.denominatorLowerStable, data.numeratorUpperStable,
        data.denominatorUpperStable⟩
      ⟨nonzero, numeratorLowerStable, denominatorLowerStable,
        numeratorUpperStable, denominatorUpperStable⟩

/-- Re-center at the exact left endpoint and recover the one-sided endpoint
index used by the constructive product table. -/
theorem index_eq_leftEndpointIndex2
    {R S : Polynomial} {interval : Interval}
    (data : CauchyEventSigns R S interval)
    (pairNonzero : R.eval interval.lower ≠ 0 ∨
      S.eval interval.lower ≠ 0)
    (numeratorStable : R.eval interval.lower = 0 ∨
      0 < R.eval interval.lower * R.eval interval.upper)
    (denominatorStable : S.eval interval.lower = 0 ∨
      0 < S.eval interval.lower * S.eval interval.upper) :
    cauchyIndex2 R S interval.lower interval.upper =
      leftEndpointIndex2
        (R.eval interval.lower) (S.eval interval.lower)
        (R.eval interval.upper) (S.eval interval.upper) := by
  let centered := data.recenter
    (FiniteSign.ofCoordinate (R.eval interval.lower))
    (FiniteSign.ofCoordinate (S.eval interval.lower))
    (by simpa only [FiniteSign.ofCoordinate_ne_zero_iff] using pairNonzero)
    (Or.inr rfl) (Or.inr rfl)
    (finiteSign_stable_of_eq_zero_or_mul_pos numeratorStable)
    (finiteSign_stable_of_eq_zero_or_mul_pos denominatorStable)
  have centeredIndex := centered.index
  dsimp only [centered, recenter] at centeredIndex
  rw [centeredIndex, FiniteSign.eventIndex2_self_left,
    finiteSign_leftEndpointIndex2_ofCoordinate]

/-- Re-center at the exact right endpoint.  After reversing orientation, the
same finite event record is the one-sided endpoint index toward the left. -/
theorem reverseIndex_eq_leftEndpointIndex2
    {R S : Polynomial} {interval : Interval}
    (data : CauchyEventSigns R S interval)
    (pairNonzero : R.eval interval.upper ≠ 0 ∨
      S.eval interval.upper ≠ 0)
    (numeratorStable : R.eval interval.upper = 0 ∨
      0 < R.eval interval.upper * R.eval interval.lower)
    (denominatorStable : S.eval interval.upper = 0 ∨
      0 < S.eval interval.upper * S.eval interval.lower) :
    cauchyIndex2 R S interval.upper interval.lower =
      leftEndpointIndex2
        (R.eval interval.upper) (S.eval interval.upper)
        (R.eval interval.lower) (S.eval interval.lower) := by
  let centered := data.recenter
    (FiniteSign.ofCoordinate (R.eval interval.upper))
    (FiniteSign.ofCoordinate (S.eval interval.upper))
    (by simpa only [FiniteSign.ofCoordinate_ne_zero_iff] using pairNonzero)
    (finiteSign_stable_of_eq_zero_or_mul_pos numeratorStable)
    (finiteSign_stable_of_eq_zero_or_mul_pos denominatorStable)
    (Or.inr rfl) (Or.inr rfl)
  have centeredIndex := centered.index
  dsimp only [centered, recenter] at centeredIndex
  rw [cauchyIndex2_reverse, centeredIndex,
    FiniteSign.neg_eventIndex2_self_right,
    finiteSign_leftEndpointIndex2_ofCoordinate]

end CauchyEventSigns

/-- Executable finite event classifier for one displayed Cauchy pair.  It
first recognizes a neutral full chain; otherwise it recognizes a fixed
numerator followed by a neutral recursively emitted tail. -/
def cauchyEventSigns?
    (R S : Polynomial) (interval : Interval) :
    Option (CauchyEventSigns R S interval) :=
  match RFAP.IntervalSign.certificate? S interval,
      neutralChainCertificates? interval (signedRemainderChain S R) with
  | some denominator, some chain => some (.ofNeutral denominator chain)
  | _, _ =>
      match RFAP.IntervalSign.certificate? R interval,
          neutralChainCertificates? interval
            (signedRemainderChain R (-((divMod S R).remainder))) with
      | some numerator, some tail =>
          some (.ofResolvedNumerator numerator tail)
      | _, _ => none

/-- The proof-bearing branch chosen by the finite Cauchy-event scanner.
Unlike `CauchyEventSigns`, this record retains the strict-sign certificate
whose existence made the branch executable.  The neutral branch therefore
provides a quantitative certificate that the denominator polynomial has no
zero throughout the displayed cell. -/
inductive CauchyEventResolution
    (R S : Polynomial) (interval : Interval) where
  | neutral
      (denominator : Certificate S interval)
      (chain : NeutralChainCertificates interval
        (signedRemainderChain S R))
  | numerator
      (certificate : Certificate R interval)
      (tail : NeutralChainCertificates interval
        (signedRemainderChain R (-((divMod S R).remainder))))

namespace CauchyEventResolution

def signs
    {R S : Polynomial} {interval : Interval}
    (resolution : CauchyEventResolution R S interval) :
    CauchyEventSigns R S interval :=
  match resolution with
  | .neutral denominator chain => .ofNeutral denominator chain
  | .numerator certificate tail => .ofResolvedNumerator certificate tail

/-- A nonzero resolved Cauchy event forces the displayed denominator to
have opposite signs, or to vanish, at the two rational endpoints.  This is
the finite sign-crossing fact needed for quantitative event approximation;
it does not introduce a zero of the denominator between the endpoints. -/
theorem denominator_endpoint_mul_nonpos_of_index_ne_zero
    {R S : Polynomial} {interval : Interval}
    (resolution : CauchyEventResolution R S interval)
    (indexNonzero : cauchyIndex2 R S
      interval.lower interval.upper ≠ 0) :
    S.eval interval.lower * S.eval interval.upper ≤ 0 := by
  cases resolution with
  | neutral denominator chain =>
      exact (indexNonzero chain.cauchyIndex2_eq_zero).elim
  | numerator certificate tail =>
      by_contra productNotNonpositive
      have productPositive :
          0 < S.eval interval.lower * S.eval interval.upper :=
        lt_of_not_ge productNotNonpositive
      have denominatorSigns :
          sign (S.eval interval.lower) = sign (S.eval interval.upper) :=
        sign_eq_of_mul_pos productPositive
      have numeratorSigns :
          sign (R.eval interval.lower) = sign (R.eval interval.upper) :=
        sign_eq_of_mul_pos certificate.endpoint_stable
      apply indexNonzero
      rw [cauchyIndex2_eq_firstJumps_of_neutralTail
        certificate.polynomial_nonzero tail]
      unfold signJump
      rw [denominatorSigns, numeratorSigns]
      exact Int.sub_self _

private theorem left_sq_le_sub_sq_of_mul_nonpos
    {left right : Coordinate} (product : left * right ≤ 0) :
    left ^ 2 ≤ (left - right) ^ 2 := by
  have crossNonpositive : 2 * (left * right) ≤ 0 := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct product
        (show (0 : Coordinate) ≤ 2 by decide)
    simpa only [RFAP.ConstructiveFraction.mul_zero_direct] using scaled
  have extraNonnegative : 0 ≤ right ^ 2 - 2 * (left * right) :=
    RFAP.ConstructiveFraction.sub_nonneg_direct
      (crossNonpositive.trans
        (RFAP.ConstructiveFraction.sq_nonneg_direct right))
  have enlarged :=
    RFAP.ConstructiveFraction.add_le_add_right_direct extraNonnegative
      (left ^ 2)
  calc
    left ^ 2 ≤ left ^ 2 + (right ^ 2 - 2 * (left * right)) := by
      simpa only [zero_add, RFAP.ConstructiveFraction.add_comm] using enlarged
    _ = (left - right) ^ 2 := by ring1

private theorem add_sq_le_two_sum_sq (left right : Coordinate) :
    (left + right) ^ 2 ≤ 2 * (left ^ 2 + right ^ 2) := by
  have squareNonnegative : 0 ≤ (left - right) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct (left - right)
  have enlarged :=
    RFAP.ConstructiveFraction.add_le_add_right_direct squareNonnegative
      ((left + right) ^ 2)
  calc
    (left + right) ^ 2 ≤ (left + right) ^ 2 + (left - right) ^ 2 :=
      by simpa only [zero_add, RFAP.ConstructiveFraction.add_comm] using enlarged
    _ = 2 * (left ^ 2 + right ^ 2) := by ring1

/-- The lower-endpoint denominator value of a nonzero resolved event is
quadratically small in the displayed cell width, with a coefficient obtained
by the existing finite Horner scan. -/
theorem denominator_lower_eval_sq_le
    {R S : Polynomial} {interval : Interval}
    (resolution : CauchyEventResolution R S interval)
    (indexNonzero : cauchyIndex2 R S
      interval.lower interval.upper ≠ 0) :
    S.eval interval.lower ^ 2 ≤
      RFAP.IntervalSign.denseEvalSqLipschitzBound S interval *
        (interval.upper - interval.lower) ^ 2 := by
  have product :=
    resolution.denominator_endpoint_mul_nonpos_of_index_ne_zero indexNonzero
  have endpoint := left_sq_le_sub_sq_of_mul_nonpos product
  have difference := RFAP.IntervalSign.eval_sub_sq_le S interval
    (⟨le_rfl, interval.valid⟩ : interval.Contains interval.lower)
    (⟨interval.valid, le_rfl⟩ : interval.Contains interval.upper)
  calc
    S.eval interval.lower ^ 2 ≤
        (S.eval interval.lower - S.eval interval.upper) ^ 2 := endpoint
    _ ≤ RFAP.IntervalSign.denseEvalSqLipschitzBound S interval *
        (interval.lower - interval.upper) ^ 2 := difference
    _ = RFAP.IntervalSign.denseEvalSqLipschitzBound S interval *
        (interval.upper - interval.lower) ^ 2 := by
      rw [show interval.lower - interval.upper =
          -(interval.upper - interval.lower) by ring1, neg_sq]

/-- Every displayed parameter in a nonzero resolved event has a denominator
residual bounded by four times the finite Horner coefficient times width
squared.  The statement is uniform over the whole rational cell and does not
select or complete a root. -/
theorem denominator_eval_sq_le
    {R S : Polynomial} {interval : Interval}
    (resolution : CauchyEventResolution R S interval)
    (indexNonzero : cauchyIndex2 R S
      interval.lower interval.upper ≠ 0)
    (parameter : Coordinate) (inside : interval.Contains parameter) :
    S.eval parameter ^ 2 ≤
      4 * RFAP.IntervalSign.denseEvalSqLipschitzBound S interval *
        (interval.upper - interval.lower) ^ 2 := by
  let lipschitz :=
    RFAP.IntervalSign.denseEvalSqLipschitzBound S interval
  let widthSq := (interval.upper - interval.lower) ^ 2
  let scale := lipschitz * widthSq
  change S.eval parameter ^ 2 ≤ 4 * lipschitz * widthSq
  have lowerBound : S.eval interval.lower ^ 2 ≤ scale := by
    simpa only [lipschitz, widthSq, scale] using
      resolution.denominator_lower_eval_sq_le indexNonzero
  have difference := RFAP.IntervalSign.eval_sub_sq_le S interval
    inside (⟨le_rfl, interval.valid⟩ : interval.Contains interval.lower)
  have distance : (parameter - interval.lower) ^ 2 ≤
      RFAP.IntervalSign.sampleRadiusSq interval interval.lower :=
    RFAP.IntervalSign.sub_sq_le_sampleRadiusSq
      (sample := interval.lower) interval inside
  have lipschitzNonnegative : 0 ≤ lipschitz := by
    simpa only [lipschitz] using
      (RFAP.IntervalSign.denseHornerSqBounds_nonneg S interval).2
  have scaledDistance :
      lipschitz * (parameter - interval.lower) ^ 2 ≤ scale := by
    calc
      lipschitz * (parameter - interval.lower) ^ 2 ≤
          lipschitz *
            RFAP.IntervalSign.sampleRadiusSq interval interval.lower :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct distance
          lipschitzNonnegative
      _ = scale := by
        rw [RFAP.IntervalSign.sampleRadiusSq_lower_eq_widthSq]
  have differenceBound :
      (S.eval parameter - S.eval interval.lower) ^ 2 ≤ scale :=
    difference.trans scaledDistance
  have sumBound :
      S.eval interval.lower ^ 2 +
          (S.eval parameter - S.eval interval.lower) ^ 2 ≤
        scale + scale :=
    add_le_add lowerBound differenceBound
  have doubled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct sumBound
      (show (0 : Coordinate) ≤ 2 by decide)
  calc
    S.eval parameter ^ 2 =
        (S.eval interval.lower +
          (S.eval parameter - S.eval interval.lower)) ^ 2 := by ring1
    _ ≤ 2 * (S.eval interval.lower ^ 2 +
          (S.eval parameter - S.eval interval.lower) ^ 2) :=
      add_sq_le_two_sum_sq _ _
    _ ≤ 2 * (scale + scale) := doubled
    _ = 4 * lipschitz * widthSq := by
      dsimp only [scale]
      ring1

end CauchyEventResolution

/-- The certificate-retaining scanner follows exactly the same finite branch
order as `cauchyEventSigns?`. -/
def cauchyEventResolution?
    (R S : Polynomial) (interval : Interval) :
    Option (CauchyEventResolution R S interval) :=
  match RFAP.IntervalSign.certificate? S interval,
      neutralChainCertificates? interval (signedRemainderChain S R) with
  | some denominator, some chain => some (.neutral denominator chain)
  | _, _ =>
      match RFAP.IntervalSign.certificate? R interval,
          neutralChainCertificates? interval
            (signedRemainderChain R (-((divMod S R).remainder))) with
      | some numerator, some tail => some (.numerator numerator tail)
      | _, _ => none

theorem cauchyEventResolution?_map_signs
    (R S : Polynomial) (interval : Interval) :
    (cauchyEventResolution? R S interval).map
        CauchyEventResolution.signs =
      cauchyEventSigns? R S interval := by
  unfold cauchyEventResolution? cauchyEventSigns?
  split
  · rfl
  · split <;> rfl

end RFAP.CauchyCells
