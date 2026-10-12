module
import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.RootIsolation.Power.Unit.Chain.Basic
import Purelib.RootIsolation.Power.Unit.Chain.Rotation
public import Purelib.RootIsolation.Power.Unit.Chain.Winding
import Purelib.RootIsolation.Power.Unit.Circuit.Chain
import Purelib.RootIsolation.Power.Unit.Circuit.Vertex
import Purelib.RootIsolation.Power.Unit.Circuit.Winding
public import Purelib.RootIsolation.Progressive.Power.Unit.Circuit.Loop
import Purelib.RootIsolation.Progressive.Power.Unit.Circuit.Monodromy
import Purelib.RootIsolation.Progressive.Power.Unit.Frame
import Purelib.RootIsolation.Progressive.Power.Unit.Vertex
import Purelib.Data.Fin.Bijection.Cycle
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.RootIsolation.Progressive.Braid.Relabeled.Basic
public import Purelib.RootIsolation.Progressive.Braid.Relabeled.PositiveBand
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
import Purelib.Topology.Knot.Braid.PositiveBand.Basic
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Topology.Knot.Braid.Word.Power
public import Purelib.Topology.Knot.Torus.Basic
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Topology.Knot.Braid.Word.Writhe
import Purelib.Topology.Knot.Closure.Basic

open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Progressive.Braid.Relabeled.Basic (RelabeledLoopBraid)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)
open Purelib.Topology.Knot.Braid (Word)

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

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

namespace Purelib.RootIsolation.Progressive.Braid.Power.Torus

open Purelib.Topology.Knot.Braid

/-- The exact initial rational unit vertex for the supplied positive power degree. -/
def baseVertex (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Geometry.Gaussian.UnitCircle.Basic.UnitVertex :=
  Power.Unit.Circuit.Vertex.unitCircuitVertex .first degree degreeAtLeastTwo 0

/-- Construct the original robust root-owner chamber at the retained initial unit parameter. -/
def frame (degree : RootDegree)
  (degreeAtLeastTwo : 2 ≤ degree.value) :
    Progressive.Chamber.Frame.ChamberFrame :=
  (baseVertex degree degreeAtLeastTwo).frame degree degreeAtLeastTwo

/-- The retained torus-model chamber has exactly the supplied power degree. -/
@[simp] theorem frame_degree (degree :
  RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    (frame degree degreeAtLeastTwo).degree = degree.value := by
  unfold frame Geometry.Gaussian.UnitCircle.Basic.UnitVertex.frame
  exact Progressive.Power.Unit.Frame.robustChamberFrame_degree _ _ degree _

/-- The retained torus-model chamber has a positive number of owner indices. -/
theorem frame_positive (degree :
  RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < (frame degree degreeAtLeastTwo).degree := by
  rw [frame_degree]
  exact degree.positive

/-- The fully explicit rational chamber loop for `Z^p-w`. -/
def loop (degree : RootDegree)
  (degreeAtLeastTwo : 2 ≤ degree.value) :
    ChamberPath (frame degree degreeAtLeastTwo)
      (frame degree degreeAtLeastTwo) :=
  Progressive.Power.Unit.Circuit.Loop.unitCircuitLoop degree degreeAtLeastTwo

/-- The explicit positive unit circuit permutes all retained power-family owners in one cycle. -/
theorem loop_isSingleCycle (degree :
  RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Data.Fin.Bijection.IsSingleCycle
      (loop degree degreeAtLeastTwo).monodromy := by
  unfold loop
  exact Progressive.Power.Unit.Circuit.Monodromy.unitCircuitMonodromy_isSingleCycle
    degree degreeAtLeastTwo

/-- Select the original zero-indexed root owner using the retained positive chamber degree. -/
def baseOwner (degree : RootDegree)
  (degreeAtLeastTwo : 2 ≤ degree.value) :
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
def negativeCircuitBraid (degree :
  RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    RelabeledLoopBraid (frame degree degreeAtLeastTwo)
      (loop degree degreeAtLeastTwo).reverse :=
  (oneCircuitBraid degree degreeAtLeastTwo).reverse

/-- The reversed rational circuit retains exactly the inverse original positive-band word. -/
@[simp] theorem negativeCircuitBraid_word (degree :
  RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    (negativeCircuitBraid degree degreeAtLeastTwo).word =
      (Topology.Knot.Braid.PositiveBand.Basic.positiveBand
        (frame degree degreeAtLeastTwo).degree).inverse := rfl

/-- Independent finite evidence that the chosen parameter circuit is the
positive once-around circuit. -/
theorem positive_parameter_winding (degree :
  RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Chain.Basic.UnitChain.parameterRaw
        Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        (Power.Unit.Circuit.Chain.unitCircuitChain degree degreeAtLeastTwo) = 4 :=
  Power.Unit.Circuit.Winding.unitCircuitChain_parameterRaw_eq_four
    degree degreeAtLeastTwo

/-! ## The power singularity `Z^p = w^q` -/

/-- Concatenate the original rational power-family circuit the supplied finite number of times. -/
def repeatedLoop (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) : Nat →
    ChamberPath (frame degree degreeAtLeastTwo)
      (frame degree degreeAtLeastTwo)
  | 0 => .nil _
  | circuits + 1 =>
      (repeatedLoop degree degreeAtLeastTwo circuits).append
        (loop degree degreeAtLeastTwo)

/-- The retained inverse-orbit labeling intertwines repeated owner monodromy with the original repeated positive-band
word. -/
theorem repeated_agrees (degree :
  RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (circuits : Nat)
    (position : Fin (frame degree degreeAtLeastTwo).degree) :
    (repeatedLoop degree degreeAtLeastTwo circuits).monodromy.forward
        ((oneCircuitBraid degree degreeAtLeastTwo).labeling.forward position) =
      (oneCircuitBraid degree degreeAtLeastTwo).labeling.forward
        ((Word.repeatWord
          (Topology.Knot.Braid.PositiveBand.Basic.positiveBand
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
          ChamberPath.monodromy_append _ _ _
        _ = (loop degree degreeAtLeastTwo).monodromy.forward
            ((oneCircuitBraid degree degreeAtLeastTwo).labeling.forward
              ((Word.repeatWord
                (Topology.Knot.Braid.PositiveBand.Basic.positiveBand
                  (frame degree degreeAtLeastTwo).degree)
                circuits).permutation.forward position)) := by
          rw [inductionHypothesis]
        _ = (oneCircuitBraid degree degreeAtLeastTwo).labeling.forward
            ((Topology.Knot.Braid.PositiveBand.Basic.positiveBand
              (frame degree degreeAtLeastTwo).degree).permutation.forward
              ((Word.repeatWord
                (Topology.Knot.Braid.PositiveBand.Basic.positiveBand
                  (frame degree degreeAtLeastTwo).degree)
                circuits).permutation.forward position)) :=
          (oneCircuitBraid degree degreeAtLeastTwo).agrees _
        _ = (oneCircuitBraid degree degreeAtLeastTwo).labeling.forward
            ((Word.repeatWord
              (Topology.Knot.Braid.PositiveBand.Basic.positiveBand
                (frame degree degreeAtLeastTwo).degree)
              (circuits + 1)).permutation.forward position) := by
          rw [Word.repeatWord_succ,
            Word.permutation_append]
          rfl

/-- Certify the repeated positive-band word against the repeated rational circuit using the original retained labeling.
-/
def repeatedBraid (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (circuits : Nat) :
    RelabeledLoopBraid (frame degree degreeAtLeastTwo)
      (repeatedLoop degree degreeAtLeastTwo circuits) where
  word := Word.repeatWord
    (Topology.Knot.Braid.PositiveBand.Basic.positiveBand
      (frame degree degreeAtLeastTwo).degree) circuits
  labeling := (oneCircuitBraid degree degreeAtLeastTwo).labeling
  agrees := repeated_agrees degree degreeAtLeastTwo circuits

/-- The repeated circuit braid retains exactly the original positive-band word repeated the supplied number of times. -/
@[simp] theorem repeatedBraid_word (degree :
  RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (circuits : Nat) :
    (repeatedBraid degree degreeAtLeastTwo circuits).word =
      Word.repeatWord
        (Topology.Knot.Braid.PositiveBand.Basic.positiveBand
          (frame degree degreeAtLeastTwo).degree) circuits := by
  rfl

/-- Package the original chamber degree and supplied positive repetition count as a power singularity. -/
def singularity (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value)
    (q : Nat) (qPositive : 0 < q) : Topology.Knot.Torus.Basic.PowerSingularity where
  p := (frame degree degreeAtLeastTwo).degree
  q := q
  pPositive := by rw [frame_degree]; exact degree.positive
  qPositive := qPositive

/-- The constructed power singularity retains exactly the original supplied root degree. -/
@[simp] theorem singularity_p (degree :
  RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (q : Nat) (qPositive : 0 < q) :
    (singularity degree degreeAtLeastTwo q qPositive).p = degree.value := by
  exact frame_degree degree degreeAtLeastTwo

/-- Headline bridge: the explicitly certified rational polynomial loop for
`Z^p=w^q` extracts exactly the torus word `(sigma_1...sigma_(p-1))^q`. -/
theorem repeatedBraid_word_eq_torus (degree :
  RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value)
    (q : Nat) (qPositive : 0 < q) :
    (repeatedBraid degree degreeAtLeastTwo q).word =
      (singularity degree degreeAtLeastTwo q qPositive).braidWord := by
  exact repeatedBraid_word degree degreeAtLeastTwo q

/-- The repeated rational circuit's certified braid closure equals the closure of its exact retained torus word. -/
theorem closure_eq_torus (degree :
  RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value)
    (q : Nat) (qPositive : 0 < q) :
    (repeatedBraid degree degreeAtLeastTwo q).closure =
      (singularity degree degreeAtLeastTwo q qPositive).closure := by
  unfold RelabeledLoopBraid.closure
  unfold Topology.Knot.Torus.Basic.PowerSingularity.closure
  rw [repeatedBraid_word_eq_torus degree degreeAtLeastTwo q qPositive]
  rfl

/-- The repeated circuit braid has exactly the circuit count times degree-minus-one crossings. -/
@[simp] theorem repeatedBraid_crossingCount (degree :
  RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (q : Nat) :
    (repeatedBraid degree degreeAtLeastTwo q).word.length =
      q * (degree.value - 1) := by
  rw [repeatedBraid_word, Word.repeatWord_length,
    Topology.Knot.Braid.PositiveBand.Basic.positiveBand_length, frame_degree]

/-- The repeated positive circuit braid has writhe equal to circuit count times degree-minus-one. -/
@[simp] theorem repeatedBraid_writhe (degree :
  RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (q : Nat) :
    (repeatedBraid degree degreeAtLeastTwo q).word.writhe =
      (q : Int) * (degree.value - 1 : Nat) := by
  rw [repeatedBraid_word, Word.repeatWord_writhe,
    Topology.Knot.Braid.PositiveBand.Basic.positiveBand_writhe, frame_degree]
end Purelib.RootIsolation.Progressive.Braid.Power.Torus

end
