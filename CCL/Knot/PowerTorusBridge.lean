import CCL.Knot.CycleLabeling
import CCL.Knot.ClosureComponents
import CCL.Knot.TorusInvariants
import CCL.Progressive.PowerMonodromy

/-!
# The explicit power-polynomial loop has torus-band monodromy

For every displayed degree `p >= 2`, `PowerMonodromy` supplies an explicit
rational coefficient circuit for `Z^p-w`, all of its finite Rouché chamber
steps, and a proof that the resulting owner permutation is one `p`-cycle.
Inverse-orbit labelling identifies that cycle with the cyclic predecessor,
which is exactly the endpoint permutation of the positive Artin band
`sigma_1 ... sigma_(p-1)`.

Repeating the rational circuit `q` times therefore produces the precise word
`(sigma_1 ... sigma_(p-1))^q` in the displayed labelling.  The extracted
closure is definitionally the finite torus-link model after the word theorem,
so the component, knot, surface, and Alexander interfaces apply directly.
-/

namespace CCL.Knot.PowerTorusBridge

open CCL.Knot.FiniteBraid
open CCL.Knot.CycleLabeling

abbrev ChamberFrame := CCL.FiniteMonodromy.ChamberFrame
abbrev ChamberPath := CCL.FiniteMonodromy.ChamberPath
abbrev FiniteBijection := CCL.FiniteMonodromy.FiniteBijection
abbrev RootDegree := CCL.RootPowers.RootDegree

def baseVertex (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    CCL.PowerMonodromy.UnitVertex :=
  CCL.PowerMonodromy.unitCircuitVertex .first degree degreeAtLeastTwo 0

def frame (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    ChamberFrame :=
  (baseVertex degree degreeAtLeastTwo).frame degree degreeAtLeastTwo

@[simp] theorem frame_degree (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    (frame degree degreeAtLeastTwo).degree = degree.value := by
  unfold frame CCL.PowerMonodromy.UnitVertex.frame
  exact CCL.PowerMonodromy.robustChamberFrame_degree _ _ degree _

theorem frame_positive (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < (frame degree degreeAtLeastTwo).degree := by
  rw [frame_degree]
  exact degree.positive

/-- The fully explicit rational chamber loop for `Z^p-w`. -/
def loop (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    ChamberPath (frame degree degreeAtLeastTwo)
      (frame degree degreeAtLeastTwo) :=
  CCL.PowerMonodromy.unitCircuitLoop degree degreeAtLeastTwo

theorem loop_isSingleCycle (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle
      (loop degree degreeAtLeastTwo).monodromy := by
  unfold loop
  exact CCL.PowerMonodromy.unitCircuitMonodromy_isSingleCycle
    degree degreeAtLeastTwo

def baseOwner (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (frame degree degreeAtLeastTwo).Index :=
  ⟨0, by rw [frame_degree]; exact degree.positive⟩

/-- One positive rational parameter circuit, expressed as the standard
positive Artin band in inverse-orbit owner coordinates. -/
def oneCircuitBraid (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    RelabeledLoopBraid (frame degree degreeAtLeastTwo)
      (loop degree degreeAtLeastTwo) :=
  RelabeledLoopBraid.positiveBandOfSingleCycle
    (frame_positive degree degreeAtLeastTwo)
    (loop_isSingleCycle degree degreeAtLeastTwo)
    (baseOwner degree degreeAtLeastTwo)

/-- Reversing the rational parameter circuit realizes the inverse of the
positive Artin band. -/
def negativeCircuitBraid (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    RelabeledLoopBraid (frame degree degreeAtLeastTwo)
      (loop degree degreeAtLeastTwo).reverse :=
  (oneCircuitBraid degree degreeAtLeastTwo).reverse

@[simp] theorem negativeCircuitBraid_word (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    (negativeCircuitBraid degree degreeAtLeastTwo).word =
      (CCL.Knot.TorusBraid.positiveBand
        (frame degree degreeAtLeastTwo).degree).inverse := rfl

/-- Independent finite evidence that the chosen parameter circuit is the
positive once-around circuit. -/
theorem positive_parameter_winding (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    CCL.PowerMonodromy.UnitChain.parameterRaw
        RFAP.GlobalWinding.coordinatePolynomial
        (CCL.PowerMonodromy.unitCircuitChain degree degreeAtLeastTwo) = 4 :=
  CCL.PowerMonodromy.unitCircuitChain_parameterRaw_eq_four
    degree degreeAtLeastTwo

/-! ## The power singularity `Z^p = w^q` -/

def repeatedLoop (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) : Nat →
    ChamberPath (frame degree degreeAtLeastTwo)
      (frame degree degreeAtLeastTwo)
  | 0 => .nil _
  | circuits + 1 =>
      (repeatedLoop degree degreeAtLeastTwo circuits).append
        (loop degree degreeAtLeastTwo)

theorem repeated_agrees (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (circuits : Nat)
    (position : Fin (frame degree degreeAtLeastTwo).degree) :
    (repeatedLoop degree degreeAtLeastTwo circuits).monodromy.forward
        ((oneCircuitBraid degree degreeAtLeastTwo).labeling.forward position) =
      (oneCircuitBraid degree degreeAtLeastTwo).labeling.forward
        ((CCL.Knot.TorusBraid.repeatWord
          (CCL.Knot.TorusBraid.positiveBand
            (frame degree degreeAtLeastTwo).degree) circuits).permutation.forward
          position) := by
  induction circuits generalizing position with
  | zero => rfl
  | succ circuits inductionHypothesis =>
      calc
        (repeatedLoop degree degreeAtLeastTwo (circuits + 1)).monodromy.forward
            ((oneCircuitBraid degree degreeAtLeastTwo).labeling.forward
              position) =
          (loop degree degreeAtLeastTwo).monodromy.forward
            ((repeatedLoop degree degreeAtLeastTwo circuits).monodromy.forward
              ((oneCircuitBraid degree degreeAtLeastTwo).labeling.forward
                position)) :=
          CCL.FiniteMonodromy.ChamberPath.monodromy_append _ _ _
        _ = (loop degree degreeAtLeastTwo).monodromy.forward
            ((oneCircuitBraid degree degreeAtLeastTwo).labeling.forward
              ((CCL.Knot.TorusBraid.repeatWord
                (CCL.Knot.TorusBraid.positiveBand
                  (frame degree degreeAtLeastTwo).degree)
                circuits).permutation.forward position)) := by
          rw [inductionHypothesis]
        _ = (oneCircuitBraid degree degreeAtLeastTwo).labeling.forward
            ((CCL.Knot.TorusBraid.positiveBand
              (frame degree degreeAtLeastTwo).degree).permutation.forward
              ((CCL.Knot.TorusBraid.repeatWord
                (CCL.Knot.TorusBraid.positiveBand
                  (frame degree degreeAtLeastTwo).degree)
                circuits).permutation.forward position)) :=
          (oneCircuitBraid degree degreeAtLeastTwo).agrees _
        _ = (oneCircuitBraid degree degreeAtLeastTwo).labeling.forward
            ((CCL.Knot.TorusBraid.repeatWord
              (CCL.Knot.TorusBraid.positiveBand
                (frame degree degreeAtLeastTwo).degree)
              (circuits + 1)).permutation.forward position) := by
          rw [CCL.Knot.TorusBraid.repeatWord_succ,
            CCL.Knot.FiniteBraid.Word.permutation_append]
          rfl

def repeatedBraid (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (circuits : Nat) :
    RelabeledLoopBraid (frame degree degreeAtLeastTwo)
      (repeatedLoop degree degreeAtLeastTwo circuits) where
  word := CCL.Knot.TorusBraid.repeatWord
    (CCL.Knot.TorusBraid.positiveBand
      (frame degree degreeAtLeastTwo).degree) circuits
  labeling := (oneCircuitBraid degree degreeAtLeastTwo).labeling
  agrees := repeated_agrees degree degreeAtLeastTwo circuits

@[simp] theorem repeatedBraid_word (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (circuits : Nat) :
    (repeatedBraid degree degreeAtLeastTwo circuits).word =
      CCL.Knot.TorusBraid.repeatWord
        (CCL.Knot.TorusBraid.positiveBand
          (frame degree degreeAtLeastTwo).degree) circuits := by
  rfl

def singularity (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value)
    (q : Nat) (qPositive : 0 < q) : CCL.Knot.TorusBraid.PowerSingularity where
  p := (frame degree degreeAtLeastTwo).degree
  q := q
  pPositive := by rw [frame_degree]; exact degree.positive
  qPositive := qPositive

@[simp] theorem singularity_p (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (q : Nat) (qPositive : 0 < q) :
    (singularity degree degreeAtLeastTwo q qPositive).p = degree.value := by
  exact frame_degree degree degreeAtLeastTwo

/-- Headline bridge: the explicitly certified rational polynomial loop for
`Z^p=w^q` extracts exactly the torus word `(sigma_1...sigma_(p-1))^q`. -/
theorem repeatedBraid_word_eq_torus (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value)
    (q : Nat) (qPositive : 0 < q) :
    (repeatedBraid degree degreeAtLeastTwo q).word =
      (singularity degree degreeAtLeastTwo q qPositive).braidWord := by
  exact repeatedBraid_word degree degreeAtLeastTwo q

theorem closure_eq_torus (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value)
    (q : Nat) (qPositive : 0 < q) :
    (repeatedBraid degree degreeAtLeastTwo q).closure =
      (singularity degree degreeAtLeastTwo q qPositive).closure := by
  unfold RelabeledLoopBraid.closure
  unfold CCL.Knot.TorusBraid.PowerSingularity.closure
  rw [repeatedBraid_word_eq_torus degree degreeAtLeastTwo q qPositive]
  rfl

@[simp] theorem repeatedBraid_crossingCount (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (q : Nat) :
    (repeatedBraid degree degreeAtLeastTwo q).word.length =
      q * (degree.value - 1) := by
  rw [repeatedBraid_word, CCL.Knot.TorusBraid.repeatWord_length,
    CCL.Knot.TorusBraid.positiveBand_length, frame_degree]

@[simp] theorem repeatedBraid_writhe (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (q : Nat) :
    (repeatedBraid degree degreeAtLeastTwo q).word.writhe =
      (q : Int) * (degree.value - 1 : Nat) := by
  rw [repeatedBraid_word, CCL.Knot.TorusBraid.repeatWord_writhe,
    CCL.Knot.TorusBraid.positiveBand_writhe, frame_degree]

/-- The explicit polynomial closure inherits the exact constructive
`gcd(p,q)` component certificate of the torus-link model. -/
def componentCertificate (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value)
    (q : Nat) (qPositive : 0 < q) :
    CCL.Knot.ClosureComponents.Closure.UniformComponentCertificate
      (repeatedBraid degree degreeAtLeastTwo q).closure := by
  rw [closure_eq_torus degree degreeAtLeastTwo q qPositive]
  exact CCL.Knot.TorusBraid.PowerSingularity.componentCertificate
    (singularity degree degreeAtLeastTwo q qPositive)

/-- The familiar genus value attached to the explicit coprime polynomial
closure's canonical positive-braid surface. -/
def canonicalGenus (degree : RootDegree) (q : Nat) : Nat :=
  CCL.Knot.TorusInvariants.canonicalGenus degree.value q

/-- The finite semigroup/Alexander coefficient table attached to the
explicit power-polynomial closure. -/
def alexanderPolynomial (degree : RootDegree) (q : Nat) : List Int :=
  CCL.Knot.TorusInvariants.alexanderPolynomial degree.value q

theorem closure_isKnot_of_gcdOne (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value)
    (q : Nat) (qPositive : 0 < q)
    (gcdOne :
      (RFAP.CanonicalGCD.compute degree.value q).gcd = 1) :
    (repeatedBraid degree degreeAtLeastTwo q).closure.IsKnot := by
  rw [closure_eq_torus degree degreeAtLeastTwo q qPositive]
  apply CCL.Knot.TorusKnot.PowerSingularity.closure_isKnot_of_gcdOne
  change (RFAP.CanonicalGCD.compute
    (frame degree degreeAtLeastTwo).degree q).gcd = 1
  rw [frame_degree]
  exact gcdOne

end CCL.Knot.PowerTorusBridge
