import CCL.Arithmetic.BoxedNames
import CCL.Progressive.TransducerGrammar

/-!
# Boxed CCL names as arithmetic enclosure processes

This is the deliberate one-way bridge from an ordinary raw CCL word plus a
finite rational box sidecar to the generic arithmetic process.  The raw
encoder, parser, and boxed-name definitions do not import this module.
-/

namespace CCL.BoxedNameProcess

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev ProgressiveName := CCL.BoxedNames.ProgressiveName
abbrev Process := CCL.ProgressiveEnclosures.Process
abbrev Named := CCL.ProgressiveTransducer.Named

/-- Positive affine radius request whose square is strictly below a positive
squared-error target.  The cap at one makes the proof uniform for large and
small targets without extracting a square root. -/
def accuracyRadius (target : Coordinate) : Coordinate :=
  min 1 (target / 4)

theorem accuracyRadius_pos {target : Coordinate} (positive : 0 < target) :
    0 < accuracyRadius target := by
  exact lt_min (by decide)
    (RFAP.ConstructiveFraction.div_pos_direct positive (by decide))

theorem accuracyRadius_sq_lt {target : Coordinate} (positive : 0 < target) :
    accuracyRadius target ^ 2 < target := by
  let radius := accuracyRadius target
  have radiusPositive : 0 < radius := accuracyRadius_pos positive
  have radiusLeOne : radius ≤ 1 := min_le_left _ _
  have radiusLeQuarter : radius ≤ target / 4 := min_le_right _ _
  have radiusSquareLe : radius ^ 2 ≤ radius := by
    rw [pow_two]
    exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      radiusLeOne radiusPositive.le).trans_eq
        (RFAP.ConstructiveFraction.one_mul radius)
  have radiusLtFourRadius : radius < 4 * radius := by
    calc
      radius = 1 * radius :=
        (RFAP.ConstructiveFraction.one_mul radius).symm
      _ < 4 * radius :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          (by decide) radiusPositive
  have fourRadiusLe : 4 * radius ≤ target := by
    have divided :=
      (RFAP.ConstructiveFraction.le_div_iff_pos
        (by decide : (0 : Coordinate) < 4)).mp radiusLeQuarter
    calc
      4 * radius = radius * 4 :=
        RFAP.ConstructiveFraction.mul_comm _ _
      _ ≤ target := divided
  exact radiusSquareLe.trans_lt (radiusLtFourRadius.trans_le fourRadiusLe)

namespace ProgressiveName

/-- Forget the raw-word field only after retaining it in the process
possibility predicate.  Each process candidate is therefore still certified
by the current ordinary CCL prefix as well as by its rational box. -/
def toProcess (name : ProgressiveName) : Process where
  State := name.State
  ball state :=
    CCL.ArithmeticEnclosures.Ball.ofBox
      (name.certificate state).box
  Possible state value := (name.certificate state).Possible value
  witness state :=
    ⟨(name.certificate state).witness,
      (name.certificate state).witness_nonzero,
      (name.certificate state).witness_represented⟩
  possible_inside := by
    intro state value possible
    exact CCL.ArithmeticEnclosures.Ball.contains_ofBox
      ((name.certificate state).possible_inside possible)
  refine state target positive :=
    name.request state (accuracyRadius target) (accuracyRadius_pos positive)
  refine_persists := by
    intro state target positive value possible
    exact (name.request_refines state (accuracyRadius target)
      (accuracyRadius_pos positive)).possible_persists possible
  accurate := by
    intro state target positive
    exact (name.accurate state (accuracyRadius target)
      (accuracyRadius_pos positive)).trans_lt
        (accuracyRadius_sq_lt positive)
  centerBound := (name.certificate name.initial).box.normSqBound
  centerBound_nonneg :=
    (name.certificate name.initial).box.normSqBound_nonneg
  center_bounded := by
    intro state
    exact (name.certificate name.initial).box.normSq_le_normSqBound
      ((name.refinesInitial state).box.contains
        (name.certificate state).box.contains_anchor)

@[simp] theorem toProcess_ball (name : ProgressiveName) (state : name.State) :
    name.toProcess.ball state =
      CCL.ArithmeticEnclosures.Ball.ofBox
        (name.certificate state).box := rfl

@[simp] theorem toProcess_possible (name : ProgressiveName)
    (state : name.State) (value : Gaussian) :
    name.toProcess.Possible state value ↔
      (name.certificate state).Possible value := by
  rfl

/-- Arithmetic entry point at the initial finite boxed certificate. -/
def toNamed (name : ProgressiveName) : Named :=
  { process := name.toProcess
    state := name.initial }

/-- Every progressive boxed CCL name therefore has an unconditionally
productive ordinary raw-bit arithmetic output cursor. -/
theorem output_productive (name : ProgressiveName) (count : Nat) :
    (name.toNamed.machine).emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          name.toNamed.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          name.toNamed.machine count).emitted.length = count :=
  name.toNamed.productive count

/-- Uniform finite denominator separation for every rational point of every
returned box.  Division remains explicitly partial at a possible zero. -/
structure Apart (name : ProgressiveName) where
  lowerSq : Coordinate
  positive : 0 < lowerSq
  lower : ∀ (state : name.State) {value : Gaussian},
    (CCL.ArithmeticEnclosures.Ball.ofBox
      (name.certificate state).box).Contains value → lowerSq ≤
      RFAP.ConstructiveGaussian.Gaussian.normSq value

namespace Apart

def toProcessApart {name : ProgressiveName} (apart : Apart name) :
    CCL.ProgressiveEnclosures.Process.Apart name.toProcess :=
  { lowerSq := apart.lowerSq
    positive := apart.positive
    lower := by
      intro state value inside
      exact apart.lower state (by simpa only [ProgressiveName.toProcess_ball]
        using inside) }

def toNamedApart {name : ProgressiveName} (apart : Apart name) :
    CCL.ProgressiveTransducer.Named.Apart name.toNamed :=
  { certificate := apart.toProcessApart }

end Apart

/-- Elementary arithmetic outputs built from two boxed CCL input names. -/
def addOutput (left right : ProgressiveName) : Named :=
  left.toNamed.add right.toNamed

def subOutput (left right : ProgressiveName) : Named :=
  left.toNamed.sub right.toNamed

def mulOutput (left right : ProgressiveName) : Named :=
  left.toNamed.mul right.toNamed

def divOutput (left right : ProgressiveName) (apart : Apart right) : Named :=
  left.toNamed.div right.toNamed apart.toNamedApart

theorem add_output_productive (left right : ProgressiveName) (count : Nat) :
    (addOutput left right).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (addOutput left right).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (addOutput left right).machine count).emitted.length = count :=
  (addOutput left right).productive count

theorem sub_output_productive (left right : ProgressiveName) (count : Nat) :
    (subOutput left right).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (subOutput left right).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (subOutput left right).machine count).emitted.length = count :=
  (subOutput left right).productive count

theorem mul_output_productive (left right : ProgressiveName) (count : Nat) :
    (mulOutput left right).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (mulOutput left right).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (mulOutput left right).machine count).emitted.length = count :=
  (mulOutput left right).productive count

theorem div_output_productive (left right : ProgressiveName)
    (apart : Apart right) (count : Nat) :
    (divOutput left right apart).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (divOutput left right apart).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (divOutput left right apart).machine count).emitted.length = count :=
  (divOutput left right apart).productive count

/-- The arithmetic results above produce the original raw syntax as well as
being productive; their squared-error sidecars never become extra symbols. -/
theorem add_output_grammar (left right : ProgressiveName) (count : Nat) :
    CCL.ProgressiveTransducerGrammar.Machine.GrammarInvariant
      (CCL.ProgressiveTransducer.advance
        (addOutput left right).machine count) :=
  CCL.ProgressiveTransducerGrammar.Named.machine_advance_invariant
    (addOutput left right) count

theorem sub_output_grammar (left right : ProgressiveName) (count : Nat) :
    CCL.ProgressiveTransducerGrammar.Machine.GrammarInvariant
      (CCL.ProgressiveTransducer.advance
        (subOutput left right).machine count) :=
  CCL.ProgressiveTransducerGrammar.Named.machine_advance_invariant
    (subOutput left right) count

theorem mul_output_grammar (left right : ProgressiveName) (count : Nat) :
    CCL.ProgressiveTransducerGrammar.Machine.GrammarInvariant
      (CCL.ProgressiveTransducer.advance
        (mulOutput left right).machine count) :=
  CCL.ProgressiveTransducerGrammar.Named.machine_advance_invariant
    (mulOutput left right) count

theorem div_output_grammar (left right : ProgressiveName)
    (apart : Apart right) (count : Nat) :
    CCL.ProgressiveTransducerGrammar.Machine.GrammarInvariant
      (CCL.ProgressiveTransducer.advance
        (divOutput left right apart).machine count) :=
  CCL.ProgressiveTransducerGrammar.Named.machine_advance_invariant
    (divOutput left right apart) count

end ProgressiveName

end CCL.BoxedNameProcess
