import CCL.Encoding.PrefixTower
import RFAP.Approximation.RobustCriticalRun

/-!
# Finite CCL prefixes for robust approximation-sharpness runs

The RFAP construction can compute any requested finite same-source run, but
its displayed rational source depends on the final run length.  This module
therefore reserves one finite final run before exposing intermediate states.
Every state uses the same robust box, rational sample, and complete finite CCL
encoding, and reveals only initial segments of the reserved windows and word.
This is the finite prefix-coherent statement: it neither forms an infinite
stream nor asserts compatibility between independently constructed final
runs.
-/

namespace CCL.ApproximationSharpness

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box
abbrev Fraction := CCL.Integral.Frac
abbrev Word := List Bool
abbrev BadWindow := RFAP.DynamicalSharpness.BadWindow

/-- Direct finite-list proof that increasing a take length extends the
prefix.  The upstream convenience theorem routes through a generic
elementwise prefix characterization whose proof closure imports
Classical choice and quotient soundness; this elementary append witness does
not. -/
private theorem takePrefixTakeDirect
    {item : Type} :
    (values : List item) → (earlier later : Nat) → earlier ≤ later →
      (values.take earlier).IsPrefix (values.take later)
  | values, 0, later, _order => ⟨values.take later, rfl⟩
  | [], _earlier + 1, 0, order => nomatch order
  | [], _earlier + 1, _later + 1, _order => ⟨[], rfl⟩
  | _head :: _tail, _earlier + 1, 0, order => nomatch order
  | head :: tail, earlier + 1, later + 1, order => by
      rcases takePrefixTakeDirect tail earlier later
          (Nat.le_of_succ_le_succ order) with ⟨suffix, prefixProof⟩
      exact ⟨suffix, congrArg (head :: ·) prefixProof⟩

/-- One explicitly finite reserve from which coherent window and CCL prefixes
are exposed.  The encoder is run once on one computed nonzero rational sample
of the common robust box. -/
structure ReservedTower
    (threshold : Coordinate) (requestedScale totalWindows : Nat) where
  robust : RFAP.RobustCriticalRun.FullyRobustRun
    threshold requestedScale totalWindows
  sample : RFAP.Boxes.Box.NonzeroSample robust.box
  fraction : Fraction
  fractionValue : fraction.value = sample.point
  numeratorNonzero : fraction.num ≠ 0
  fullWord : Word
  fullWord_eq : fullWord = CCL.Encoder.encode fraction numeratorNonzero

/-- Compute a finite prefix reserve from the fully robust RFAP run. -/
def reserve
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale totalWindows : Nat) :
    ReservedTower threshold requestedScale totalWindows := by
  let robust := RFAP.RobustCriticalRun.criticalFullyRobustRun
    certificate requestedScale totalWindows
  let sample := robust.box.nonzeroSample robust.proper
  let fraction := CCL.Integral.Frac.ofGaussian sample.point
  let numeratorNonzero :=
    CCL.Integral.Frac.ofGaussian_num_ne_zero sample.nonzero
  exact
    { robust := robust
      sample := sample
      fraction := fraction
      fractionValue := CCL.Integral.Frac.ofGaussian_value sample.point
      numeratorNonzero := numeratorNonzero
      fullWord := CCL.Encoder.encode fraction numeratorNonzero
      fullWord_eq := rfl }

namespace ReservedTower

/-- A state records how much of the already computed finite reserve has been
revealed.  Both bounds are data, so all later prefix statements are ordinary
finite-list calculations. -/
structure Stage
    {threshold : Coordinate} {requestedScale totalWindows : Nat}
    (tower : ReservedTower threshold requestedScale totalWindows) where
  scale : Nat
  scaleBound : scale ≤ requestedScale
  windowCount : Nat
  windowBound : windowCount ≤ totalWindows
  bitCount : Nat
  bitBound : bitCount ≤ tower.fullWord.length

namespace Stage

variable {threshold : Coordinate} {requestedScale totalWindows : Nat}
variable {tower : ReservedTower threshold requestedScale totalWindows}

/-- Every stage retains the one robust box fixed by the reserve. -/
def box (_stage : Stage tower) : Box := tower.robust.box

/-- The currently revealed initial segment of certified bad windows. -/
def windows (stage : Stage tower) :
    List { window : BadWindow threshold requestedScale //
      window.source = tower.robust.exact.source } :=
  tower.robust.exact.windows.take stage.windowCount

/-- The currently revealed initial segment of the sample's finite CCL word. -/
def word (stage : Stage tower) : Word :=
  tower.fullWord.take stage.bitCount

theorem windows_length (stage : Stage tower) :
    stage.windows.length = stage.windowCount := by
  apply List.length_take_of_le
  rw [tower.robust.exact.length_eq]
  exact stage.windowBound

theorem word_length (stage : Stage tower) :
    stage.word.length = stage.bitCount :=
  List.length_take_of_le stage.bitBound

/-- The displayed rational sample remains in the stage box. -/
theorem sample_inside (stage : Stage tower) :
    stage.box.Contains tower.sample.point :=
  tower.sample.inside

/-- The displayed sample is exactly the value encoded by the stage prefix. -/
theorem fraction_value (_stage : Stage tower) :
    tower.fraction.value = tower.sample.point :=
  tower.fractionValue

/-- Every revealed window lies beyond the scale currently exposed by the
stage.  The reserve constructs the stronger bound at its final scale. -/
theorem beyondScale (stage : Stage tower)
    (window : { window : BadWindow threshold requestedScale //
      window.source = tower.robust.exact.source }) :
    stage.scale < RFAP.BestApproximation.denominatorQuadrance
      window.1.upper := by
  have reserved := window.1.beyondScale
  exact stage.scaleBound.trans_lt reserved

/-- Each revealed word is a genuine CCL prefix cylinder for the displayed
rational sample. -/
theorem cylinder (stage : Stage tower) :
    CCL.PrefixTower.Cylinder stage.word tower.fraction
      tower.numeratorNonzero := by
  unfold word CCL.PrefixTower.Cylinder
  rw [tower.fullWord_eq]
  exact List.take_prefix stage.bitCount
    (CCL.Encoder.encode tower.fraction tower.numeratorNonzero)

/-- Every revealed window remains consecutive best throughout the common
robust source box. -/
theorem uniformConsecutive (stage : Stage tower)
    (sample : Gaussian) (inside : stage.box.Contains sample)
    (window : { window : BadWindow threshold requestedScale //
      window.source = tower.robust.exact.source })
    (member : window ∈ stage.windows) :
    RFAP.BestApproximation.AreConsecutiveBest sample
      window.1.lower window.1.upper := by
  apply tower.robust.uniformConsecutive sample inside window
  exact (List.take_prefix stage.windowCount
    tower.robust.exact.windows).subset member

/-- Every revealed window violates the sharper Dirichlet-window threshold
uniformly throughout the common robust source box. -/
theorem uniformViolation (stage : Stage tower)
    (sample : Gaussian) (inside : stage.box.Contains sample)
    (window : { window : BadWindow threshold requestedScale //
      window.source = tower.robust.exact.source })
    (member : window ∈ stage.windows) :
    1 < threshold *
      RFAP.BestApproximation.dirichletWindowQuadrance sample
        window.1.lower window.1.upper := by
  apply tower.robust.uniformViolation sample inside window
  exact (List.take_prefix stage.windowCount
    tower.robust.exact.windows).subset member

/-- Upper denominator quadrances remain strictly increasing in every
revealed initial segment. -/
theorem scalesStrict (stage : Stage tower) :
    stage.windows.Pairwise fun earlier later =>
      RFAP.BestApproximation.denominatorQuadrance earlier.1.upper <
        RFAP.BestApproximation.denominatorQuadrance later.1.upper :=
  tower.robust.exact.scalesStrict.take

end Stage

/-- Reveal at most the requested number of reserved windows and encoded bits.
Requests past either explicit finite reserve are saturated at its endpoint. -/
def stage
    {threshold : Coordinate} {requestedScale totalWindows : Nat}
    (tower : ReservedTower threshold requestedScale totalWindows)
    (revealedScale requestedWindows requestedBits : Nat) : Stage tower where
  scale := min revealedScale requestedScale
  scaleBound := Nat.min_le_right _ _
  windowCount := min requestedWindows totalWindows
  windowBound := Nat.min_le_right _ _
  bitCount := min requestedBits tower.fullWord.length
  bitBound := Nat.min_le_right _ _

theorem stage_scale_of_le
    {threshold : Coordinate} {requestedScale totalWindows : Nat}
    (tower : ReservedTower threshold requestedScale totalWindows)
    (revealedScale requestedWindows requestedBits : Nat)
    (within : revealedScale ≤ requestedScale) :
    (tower.stage revealedScale requestedWindows requestedBits).scale =
      revealedScale :=
  Nat.min_eq_left within

theorem stage_windowCount_of_le
    {threshold : Coordinate} {requestedScale totalWindows : Nat}
    (tower : ReservedTower threshold requestedScale totalWindows)
    (revealedScale requestedWindows requestedBits : Nat)
    (within : requestedWindows ≤ totalWindows) :
    (tower.stage revealedScale requestedWindows requestedBits).windowCount =
      requestedWindows :=
  Nat.min_eq_left within

theorem stage_bitCount_of_le
    {threshold : Coordinate} {requestedScale totalWindows : Nat}
    (tower : ReservedTower threshold requestedScale totalWindows)
    (revealedScale requestedWindows requestedBits : Nat)
    (within : requestedBits ≤ tower.fullWord.length) :
    (tower.stage revealedScale requestedWindows requestedBits).bitCount =
      requestedBits :=
  Nat.min_eq_left within

/-- The empty initial state of a finite reserve. -/
def initial
    {threshold : Coordinate} {requestedScale totalWindows : Nat}
    (tower : ReservedTower threshold requestedScale totalWindows) :
    Stage tower :=
  tower.stage 0 0 0

/-- Reveal the complete reserved run and the complete finite sample word. -/
def complete
    {threshold : Coordinate} {requestedScale totalWindows : Nat}
    (tower : ReservedTower threshold requestedScale totalWindows) :
    Stage tower :=
  tower.stage requestedScale totalWindows tower.fullWord.length

/-- Extend a stage by finite requested increments, saturating at the two
limits fixed by the reserve. -/
def Stage.extend
    {threshold : Coordinate} {requestedScale totalWindows : Nat}
    {tower : ReservedTower threshold requestedScale totalWindows}
    (current : Stage tower) (newScale additionalWindows additionalBits : Nat) :
    Stage tower :=
  tower.stage (max current.scale newScale)
    (current.windowCount + additionalWindows)
    (current.bitCount + additionalBits)

/-- Joint refinement relation for reserved finite sharpness states. -/
structure StageExtends
    {threshold : Coordinate} {requestedScale totalWindows : Nat}
    {tower : ReservedTower threshold requestedScale totalWindows}
    (earlier later : Stage tower) : Prop where
  scaleLe : earlier.scale ≤ later.scale
  boxRefines : later.box.Refines earlier.box
  wordPrefix : earlier.word.IsPrefix later.word
  windowsPrefix : earlier.windows.IsPrefix later.windows

theorem stageExtends_of_le
    {threshold : Coordinate} {requestedScale totalWindows : Nat}
    {tower : ReservedTower threshold requestedScale totalWindows}
    {earlier later : Stage tower}
    (scaleLe : earlier.scale ≤ later.scale)
    (windowsLe : earlier.windowCount ≤ later.windowCount)
    (bitsLe : earlier.bitCount ≤ later.bitCount) :
    StageExtends earlier later :=
  { scaleLe := scaleLe
    boxRefines := RFAP.Boxes.Box.refines_refl tower.robust.box
    wordPrefix :=
      takePrefixTakeDirect tower.fullWord earlier.bitCount later.bitCount bitsLe
    windowsPrefix :=
      takePrefixTakeDirect tower.robust.exact.windows
        earlier.windowCount later.windowCount windowsLe }

/-- Increasing any of the three finite requests produces a joint extension,
including when one or more requests saturate at a reserved endpoint. -/
theorem stage_monotone
    {threshold : Coordinate} {requestedScale totalWindows : Nat}
    (tower : ReservedTower threshold requestedScale totalWindows)
    {earlierScale laterScale earlierWindows laterWindows
      earlierBits laterBits : Nat}
    (scaleLe : earlierScale ≤ laterScale)
    (windowsLe : earlierWindows ≤ laterWindows)
    (bitsLe : earlierBits ≤ laterBits) :
    StageExtends
      (tower.stage earlierScale earlierWindows earlierBits)
      (tower.stage laterScale laterWindows laterBits) := by
  apply stageExtends_of_le
  · exact min_le_min scaleLe le_rfl
  · exact min_le_min windowsLe le_rfl
  · exact min_le_min bitsLe le_rfl

/-- Every finite extension preserves the box, word prefix, and previously
revealed window prefix. -/
theorem Stage.extend_extends
    {threshold : Coordinate} {requestedScale totalWindows : Nat}
    {tower : ReservedTower threshold requestedScale totalWindows}
    (current : Stage tower) (newScale additionalWindows additionalBits : Nat) :
    StageExtends current
      (current.extend newScale additionalWindows additionalBits) := by
  apply stageExtends_of_le
  · dsimp only [Stage.extend, stage]
    exact Nat.le_min_of_le_of_le
      (Nat.le_max_left current.scale newScale)
      current.scaleBound
  · dsimp only [Stage.extend, stage]
    exact Nat.le_min_of_le_of_le
      (Nat.le_add_right current.windowCount additionalWindows)
      current.windowBound
  · dsimp only [Stage.extend, stage]
    exact Nat.le_min_of_le_of_le
      (Nat.le_add_right current.bitCount additionalBits)
      current.bitBound

/-- When the requested window increment fits in the reserve, exactly that
many windows are added. -/
theorem Stage.extend_windowCount_of_fits
    {threshold : Coordinate} {requestedScale totalWindows : Nat}
    {tower : ReservedTower threshold requestedScale totalWindows}
    (current : Stage tower) (newScale additionalWindows additionalBits : Nat)
    (fits : current.windowCount + additionalWindows ≤ totalWindows) :
    (current.extend newScale additionalWindows additionalBits).windowCount =
      current.windowCount + additionalWindows :=
  Nat.min_eq_left fits

/-- When the requested bit increment fits before the terminal finite word,
exactly that many bits are added. -/
theorem Stage.extend_bitCount_of_fits
    {threshold : Coordinate} {requestedScale totalWindows : Nat}
    {tower : ReservedTower threshold requestedScale totalWindows}
    (current : Stage tower) (newScale additionalWindows additionalBits : Nat)
    (fits : current.bitCount + additionalBits ≤ tower.fullWord.length) :
    (current.extend newScale additionalWindows additionalBits).bitCount =
      current.bitCount + additionalBits :=
  Nat.min_eq_left fits

/-- A fitting extension has the advertised window-list length. -/
theorem Stage.extend_windows_length_of_fits
    {threshold : Coordinate} {requestedScale totalWindows : Nat}
    {tower : ReservedTower threshold requestedScale totalWindows}
    (current : Stage tower) (newScale additionalWindows additionalBits : Nat)
    (fits : current.windowCount + additionalWindows ≤ totalWindows) :
    (current.extend newScale additionalWindows additionalBits).windows.length =
      current.windowCount + additionalWindows := by
  rw [(current.extend newScale additionalWindows additionalBits).windows_length,
    current.extend_windowCount_of_fits newScale additionalWindows additionalBits fits]

/-- A fitting extension has the advertised finite-prefix length. -/
theorem Stage.extend_word_length_of_fits
    {threshold : Coordinate} {requestedScale totalWindows : Nat}
    {tower : ReservedTower threshold requestedScale totalWindows}
    (current : Stage tower) (newScale additionalWindows additionalBits : Nat)
    (fits : current.bitCount + additionalBits ≤ tower.fullWord.length) :
    (current.extend newScale additionalWindows additionalBits).word.length =
      current.bitCount + additionalBits := by
  rw [(current.extend newScale additionalWindows additionalBits).word_length,
    current.extend_bitCount_of_fits newScale additionalWindows additionalBits fits]

end ReservedTower

/-- Public one-call construction of a finite robust sharpness reserve with
coherent CCL-prefix stages. -/
def finiteSharpnessTower
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale totalWindows : Nat) :
    ReservedTower threshold requestedScale totalWindows :=
  reserve certificate requestedScale totalWindows

end CCL.ApproximationSharpness
