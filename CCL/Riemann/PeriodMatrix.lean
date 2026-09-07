import CCL.Riemann.AlgebraicDifferentials
import CCL.Riemann.PivotedScaledInverse
import CCL.Progressive.FiniteTable
import CCL.Arithmetic.OperationalFieldLaws

/-!
# Persistent finite period matrices

This file assembles the algebraically certified period programs into finite
`A` and `B` matrices of coherent CCL names.  It also gives a constructive
normalization interface: synchronized finite samples compute the canonical
division-free scaled inverse of `A`, and one explicit apartness witness for
its scalar constructs every entry of `A^{-1}B` by finite CCL arithmetic.
-/

namespace CCL.Riemann.PeriodMatrix

open CCL.Riemann.LiftedPaths
open CCL.Riemann.AlgebraicDifferentials

abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedMatrix (size : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Matrix CoherentNamed size
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GeometricApproximation :=
  CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation
abbrev GeometricMatrix (size : Nat) :=
  CCL.Riemann.FiniteMatrixApproximation.GeometricMatrix size

/-- The standard zero-based differential basis `dx/y, x dx/y, ...`. -/
def standardDifferential {genus : Nat} (index : Fin genus) :
    Differential genus :=
  ⟨index⟩

/-- All certified `a`- and `b`-period integration programs for one curve and
one common lifted symplectic cycle family. -/
structure PeriodData {genus : Nat} (curve : HyperellipticCurve genus) where
  cycles : LiftedSymplecticCycles 2 genus
  aProgram : forall differential cycle : Fin genus,
    CertifiedPeriodProgram curve (standardDifferential differential)
      (cycles.aCycle cycle)
  bProgram : forall differential cycle : Fin genus,
    CertifiedPeriodProgram curve (standardDifferential differential)
      (cycles.bCycle cycle)

namespace PeriodData

def aMatrix {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PeriodData curve) : NamedMatrix genus :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun differential cycle =>
    (data.aProgram differential cycle).output

def bMatrix {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PeriodData curve) : NamedMatrix genus :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun differential cycle =>
    (data.bProgram differential cycle).output

@[simp] theorem aMatrix_apply {genus : Nat}
    {curve : HyperellipticCurve genus} (data : PeriodData curve)
    (differential cycle : Fin genus) :
    data.aMatrix differential cycle =
      (data.aProgram differential cycle).output := by
  exact RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

@[simp] theorem bMatrix_apply {genus : Nat}
    {curve : HyperellipticCurve genus} (data : PeriodData curve)
    (differential cycle : Fin genus) :
    data.bMatrix differential cycle =
      (data.bProgram differential cycle).output := by
  exact RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

/-- Row-major materialization of any finite named matrix. -/
def matrixChannels {genus : Nat} (matrix : NamedMatrix genus) :
    List CoherentNamed :=
  (List.ofFn fun row : Fin genus =>
    List.ofFn fun column : Fin genus => matrix row column).flatMap id

theorem matrixEntry_mem_channels {genus : Nat} (matrix : NamedMatrix genus)
    (row column : Fin genus) :
    matrix row column ∈ matrixChannels matrix := by
  unfold matrixChannels
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨List.ofFn (fun column : Fin genus => matrix row column), ?_, ?_⟩
  · exact List.mem_ofFn.mpr ⟨row, rfl⟩
  · change matrix row column ∈
      List.ofFn (fun column : Fin genus => matrix row column)
    exact List.mem_ofFn.mpr ⟨column, rfl⟩

/-- One same-budget finite table containing both period matrices. -/
def table {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PeriodData curve) : CCL.ProgressiveFiniteTable.Table :=
  ⟨matrixChannels data.aMatrix ++ matrixChannels data.bMatrix⟩

theorem aEntry_mem_table {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (differential cycle : Fin genus) :
    data.aMatrix differential cycle ∈ data.table.channels := by
  apply List.mem_append.mpr
  exact Or.inl (matrixEntry_mem_channels data.aMatrix differential cycle)

theorem bEntry_mem_table {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (differential cycle : Fin genus) :
    data.bMatrix differential cycle ∈ data.table.channels := by
  apply List.mem_append.mpr
  exact Or.inr (matrixEntry_mem_channels data.bMatrix differential cycle)

/-- Every `A` entry answers one common table request with its enclosure,
semantic allowance, persistent bits, and exact parser certificate. -/
theorem aEntry_sharedRequest {genus : Nat}
    {curve : HyperellipticCurve genus} (data : PeriodData curve)
    (differential cycle : Fin genus)
    (target : CCL.ProgressiveFiniteTable.Coordinate) (positive : 0 < target)
    (count : Nat) :
    CCL.ProgressiveFiniteTable.RequestContract data.table.channels
      (data.aMatrix differential cycle) target positive count :=
  data.table.member_bitstream_and_allowance
    (data.aEntry_mem_table differential cycle) target positive count

/-- The corresponding same-budget contract for every `B` entry. -/
theorem bEntry_sharedRequest {genus : Nat}
    {curve : HyperellipticCurve genus} (data : PeriodData curve)
    (differential cycle : Fin genus)
    (target : CCL.ProgressiveFiniteTable.Coordinate) (positive : 0 < target)
    (count : Nat) :
    CCL.ProgressiveFiniteTable.RequestContract data.table.channels
      (data.bMatrix differential cycle) target positive count :=
  data.table.member_bitstream_and_allowance
    (data.bEntry_mem_table differential cycle) target positive count

/-- Shared finite refinement of one unnormalized A-period entry. -/
def refinedAEntry {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target)
    (differential cycle : Fin genus) : CCL.ProgressiveTransducer.Named :=
  CCL.ProgressiveFiniteTable.sharedName data.table.channels
    (data.aMatrix differential cycle) target positive

/-- Shared finite refinement of one unnormalized B-period entry. -/
def refinedBEntry {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target)
    (differential cycle : Fin genus) : CCL.ProgressiveTransducer.Named :=
  CCL.ProgressiveFiniteTable.sharedName data.table.channels
    (data.bMatrix differential cycle) target positive

/-- Displayed rational centre of one unnormalized A-period entry. -/
def aCenter {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target)
    (differential cycle : Fin genus) : Gaussian :=
  let entry := data.refinedAEntry target positive differential cycle
  (entry.process.ball entry.state).center

/-- Displayed rational centre of one unnormalized B-period entry. -/
def bCenter {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target)
    (differential cycle : Fin genus) : Gaussian :=
  let entry := data.refinedBEntry target positive differential cycle
  (entry.process.ball entry.state).center

/-- Displayed squared enclosure radius of one unnormalized A-period entry. -/
def aRadiusSq {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target)
    (differential cycle : Fin genus) : Coordinate :=
  let entry := data.refinedAEntry target positive differential cycle
  (entry.process.ball entry.state).radiusSq

/-- Displayed squared enclosure radius of one unnormalized B-period entry. -/
def bRadiusSq {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target)
    (differential cycle : Fin genus) : Coordinate :=
  let entry := data.refinedBEntry target positive differential cycle
  (entry.process.ball entry.state).radiusSq

theorem aRadiusSq_lt_target {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target)
    (differential cycle : Fin genus) :
    data.aRadiusSq target positive differential cycle < target := by
  unfold aRadiusSq refinedAEntry
  exact CCL.ProgressiveFiniteTable.sharedName_radius_lt
    data.table.channels (data.aMatrix differential cycle) positive

theorem bRadiusSq_lt_target {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target)
    (differential cycle : Fin genus) :
    data.bRadiusSq target positive differential cycle < target := by
  unfold bRadiusSq refinedBEntry
  exact CCL.ProgressiveFiniteTable.sharedName_radius_lt
    data.table.channels (data.bMatrix differential cycle) positive

/-- One finite Gaussian-rational A-period centre matrix. -/
def aCenterMatrix {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target) :
    RFAP.ConstructiveFiniteMatrix.Matrix Gaussian genus :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun differential cycle =>
    data.aCenter target positive differential cycle

/-- One finite Gaussian-rational B-period centre matrix. -/
def bCenterMatrix {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (target : Coordinate) (positive : 0 < target) :
    RFAP.ConstructiveFiniteMatrix.Matrix Gaussian genus :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun differential cycle =>
    data.bCenter target positive differential cycle

end PeriodData

/-- The productive coherent name generated directly by a synchronized finite
geometric approximation. -/
def geometricNamed (source : GeometricApproximation) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
    source.toApproximation

/-- Dropping any finite prefix of a geometric stream preserves its
operational value.  A comparison against the shifted stream is obtained by
asking reflexivity of the original stream to start the right side at the
corresponding absolute index. -/
def geometricDropEquivalent (source : GeometricApproximation)
    (anchor : Nat) :
    CCL.OperationalEquivalence.Equivalent source.toApproximation
      (source.drop anchor).toApproximation where
  compare := by
    intro leftStart rightStart target positive
    let comparison :=
      (CCL.OperationalEquivalence.Equivalent.refl source.toApproximation).compare
        leftStart (anchor + rightStart) target positive
    have anchorLeRight : anchor <= comparison.rightIndex := by
      exact (by omega0 : anchor <= anchor + rightStart).trans
        comparison.right_ge
    let shiftedRight := comparison.rightIndex - anchor
    have shiftedIdentity : anchor + shiftedRight = comparison.rightIndex := by
      dsimp only [shiftedRight]
      omega0
    exact
      { leftIndex := comparison.leftIndex
        rightIndex := shiftedRight
        left_ge := comparison.left_ge
        right_ge := by
          dsimp only [shiftedRight]
          apply Nat.le_sub_of_add_le
          simpa only [Nat.add_comm] using comparison.right_ge
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have absoluteRightOrder :
              comparison.rightIndex <= anchor + rightLater := by
            rw [<- shiftedIdentity]
            omega0
          simpa only [CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.drop_sample,
            CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.toApproximation_sample]
            using comparison.close leftOrder absoluteRightOrder }

/-- The coherent name generated by a finite tail is operationally equivalent
to the name generated by the original geometric stream. -/
def geometricNamed_drop_equivalent (source : GeometricApproximation)
    (anchor : Nat) :
    NamedEquivalent (geometricNamed source).name
      (geometricNamed (source.drop anchor)).name := by
  simpa only [geometricNamed,
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
    CCL.TranscendentalCoherence.approximationEquivalent_toNamed
      (geometricDropEquivalent source anchor)

/-- Uniform apartness of a nonzero synchronized constant approximation. -/
def geometricExactApart (value : Gaussian) (nonzero : value ≠ 0) :
    CCL.ProgressiveTransducer.Named.Apart
      (geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact
          value)).name where
  certificate :=
    { lowerSq := RFAP.ConstructiveGaussian.Gaussian.normSq value
      positive := RFAP.ConstructiveGaussian.Gaussian.normSq_pos nonzero
      lower := by
        intro state candidate inside
        change RFAP.ConstructiveGaussian.Gaussian.normSq
          (candidate - value) <=
            CCL.FiniteGeometric.quarterRadius 0 state at inside
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow] at inside
        rw [zero_mul] at inside
        have normZero : RFAP.ConstructiveGaussian.Gaussian.normSq
            (candidate - value) = 0 :=
          le_antisymm inside
            (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
        have differenceZero :=
          RFAP.ConstructiveGaussian.Gaussian.normSq_eq_zero.mp normZero
        have equal : candidate = value := sub_eq_zero.mp differenceZero
        rw [equal] }

/-- Whole-ball apartness in particular supplies the weaker genuine-candidate
apartness accepted by constructive apartification. -/
def possibleApartOfNamedApart {name : CCL.ProgressiveTransducer.Named}
    (apart : CCL.ProgressiveTransducer.Named.Apart name) :
    CCL.ProgressiveCharts.PossibleApart name.process where
  lowerSq := apart.certificate.lowerSq
  positive := apart.certificate.positive
  lower := by
    intro state value possible
    exact apart.certificate.lower state
      (name.process.possible_inside possible)

/-- Finite recursive addition of coherent names.  The empty sum uses the
same synchronized zero approximation as the matrix identities below. -/
def sumNamed : {count : Nat} -> (Fin count -> CoherentNamed) -> CoherentNamed
  | 0, _ => geometricNamed
      (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact 0)
  | count + 1, values =>
      CCL.ProgressiveCoherence.CoherentNamed.add (values 0)
        (sumNamed fun index : Fin count => values index.succ)

/-- Recursive actual CCL addition realizes the equal-index geometric sum
whenever each displayed summand realizes its synchronized approximation. -/
def sumNamed_equivalent_geometricSum {count : Nat}
    (values : Fin count -> CoherentNamed)
    (sources : Fin count -> GeometricApproximation)
    (equivalent : forall entry,
      NamedEquivalent (values entry).name
        (geometricNamed (sources entry)).name) :
    NamedEquivalent (sumNamed values).name
      (geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.sum
          sources)).name := by
  induction count with
  | zero =>
      exact CCL.OperationalEquivalence.NamedEquivalent.refl _
  | succ count inductionHypothesis =>
      let tailValues := fun entry : Fin count => values entry.succ
      let tailSources := fun entry : Fin count => sources entry.succ
      let tailSum := sumNamed tailValues
      let geometricTail := geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.sum
          tailSources)
      have tailEquivalent : NamedEquivalent tailSum.name geometricTail.name :=
        inductionHypothesis tailValues tailSources
          (fun entry => equivalent entry.succ)
      have replaceOperands : NamedEquivalent
          (CCL.ProgressiveCoherence.CoherentNamed.add
            (values 0) tailSum).name
          (CCL.ProgressiveCoherence.CoherentNamed.add
            (geometricNamed (sources 0)) geometricTail).name :=
        CCL.TranscendentalCoherence.coherentAdd_respects
          (values 0) (geometricNamed (sources 0)) tailSum geometricTail
          (equivalent 0) tailEquivalent
      apply CCL.OperationalEquivalence.NamedEquivalent.trans replaceOperands
      dsimp only [geometricTail, tailSources]
      simpa only [geometricNamed,
        CCL.ProgressiveCoherence.CoherentNamed.add,
        CCL.ProgressiveCoherence.CoherentNamed.ofApproximation,
        CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.sum] using
        CCL.OperationalFieldLaws.addToNamed_equivalent_pointwise
          (sources 0).toApproximation
          (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.sum
            tailSources).toApproximation
          (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.add
            (sources 0)
            (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.sum
              tailSources)).toApproximation
          (by intro index; rfl)

/-- Finite recursive sums respect operational equality term by term. -/
def sumNamed_respects {count : Nat}
    (left right : Fin count -> CoherentNamed)
    (equivalent : forall entry,
      NamedEquivalent (left entry).name (right entry).name) :
    NamedEquivalent (sumNamed left).name (sumNamed right).name := by
  induction count with
  | zero => exact CCL.OperationalEquivalence.NamedEquivalent.refl _
  | succ count inductionHypothesis =>
      change NamedEquivalent
        (CCL.ProgressiveCoherence.CoherentNamed.add (left 0)
          (sumNamed fun entry : Fin count => left entry.succ)).name
        (CCL.ProgressiveCoherence.CoherentNamed.add (right 0)
          (sumNamed fun entry : Fin count => right entry.succ)).name
      exact CCL.TranscendentalCoherence.coherentAdd_respects
        (left 0) (right 0)
        (sumNamed fun entry : Fin count => left entry.succ)
        (sumNamed fun entry : Fin count => right entry.succ)
        (equivalent 0)
        (inductionHypothesis
          (fun entry : Fin count => left entry.succ)
          (fun entry : Fin count => right entry.succ)
          (fun entry => equivalent entry.succ))

/-- A recursive rational bound for a finite Gaussian sum.  Its shape mirrors
`sumFin_succ`, using the explicit two-term squared-norm triangle bound at each
constructor. -/
def sumBound : {count : Nat} -> (Fin count -> Coordinate) -> Coordinate
  | 0, _ => 0
  | count + 1, bounds =>
      2 * (bounds 0 + sumBound fun index : Fin count => bounds index.succ)

theorem sumBound_nonneg {count : Nat} (bounds : Fin count -> Coordinate)
    (nonnegative : forall index, 0 <= bounds index) :
    0 <= sumBound bounds := by
  induction count with
  | zero => exact le_rfl
  | succ count inductionHypothesis =>
      change 0 <= 2 *
        (bounds 0 + sumBound (fun index : Fin count => bounds index.succ))
      exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg (nonnegative 0)
          (inductionHypothesis (fun index => bounds index.succ)
            (fun index => nonnegative index.succ)))

/-- The squared norm of a finite Gaussian sum is bounded by `sumBound` of
displayed per-entry squared-norm bounds. -/
theorem normSq_sumFin_le_sumBound {count : Nat}
    (values : Fin count -> Gaussian) (bounds : Fin count -> Coordinate)
    (bounded : forall index,
      RFAP.ConstructiveGaussian.Gaussian.normSq (values index) <= bounds index) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (RFAP.ConstructiveFiniteMatrix.sumFin values) <=
      sumBound bounds := by
  induction count with
  | zero =>
      change RFAP.ConstructiveGaussian.Gaussian.normSq 0 <= 0
      rw [RFAP.ConstructiveGaussian.Gaussian.normSq_zero]
  | succ count inductionHypothesis =>
      rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
      change RFAP.ConstructiveGaussian.Gaussian.normSq
          (values 0 + RFAP.ConstructiveFiniteMatrix.sumFin
            (fun index : Fin count => values index.succ)) <=
        2 * (bounds 0 +
          sumBound (fun index : Fin count => bounds index.succ))
      exact
        (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add (bounded 0)
              (inductionHypothesis
                (fun index : Fin count => values index.succ)
                (fun index : Fin count => bounds index.succ)
                (fun index => bounded index.succ))) (by decide))

/-- Recursive sum bounds commute with the shared quarter-power schedule. -/
theorem sumBound_quarterRadius {count : Nat}
    (scales : Fin count -> Coordinate) (index : Nat) :
    sumBound (fun entry =>
        CCL.FiniteGeometric.quarterRadius (scales entry) index) =
      CCL.FiniteGeometric.quarterRadius (sumBound scales) index := by
  induction count with
  | zero =>
      change (0 : Coordinate) = CCL.FiniteGeometric.quarterRadius 0 index
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
      ring1
  | succ count inductionHypothesis =>
      change 2 *
          (CCL.FiniteGeometric.quarterRadius (scales 0) index +
            sumBound (fun entry : Fin count =>
              CCL.FiniteGeometric.quarterRadius
                (scales entry.succ) index)) =
        CCL.FiniteGeometric.quarterRadius
          (2 * (scales 0 +
            sumBound (fun entry : Fin count => scales entry.succ))) index
      rw [inductionHypothesis (fun entry : Fin count => scales entry.succ),
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
      ring1

/-- Error scale for one synchronized finite matrix-product entry. -/
def matrixProductErrorScale {size : Nat} (left right : NamedMatrix size)
    (row column : Fin size) : Coordinate :=
  sumBound fun middle =>
    CCL.TranscendentalCoherence.sampledProductErrorScale
      (left row middle).name (right middle column).name

theorem matrixProductErrorScale_nonneg {size : Nat}
    (left right : NamedMatrix size) (row column : Fin size) :
    0 <= matrixProductErrorScale left right row column :=
  sumBound_nonneg _ fun middle =>
    CCL.TranscendentalCoherence.sampledProductErrorScale_nonneg
      (left row middle).name (right middle column).name

/-- Equal-index finite products, summed at one common index.  This diagnostic
sampler exposes synchronized readings of arbitrary named matrices; it never
silently combines entries taken from unrelated refinement levels. -/
def matrixProductApproximation {size : Nat}
    (left right : NamedMatrix size) (row column : Fin size) :
    CCL.ProgressiveApproximation.Approximation where
  sample index :=
    RFAP.ConstructiveFiniteMatrix.sumFin fun middle =>
      (CCL.TranscendentalCoherence.sampledProductApproximation
        (left row middle).name (right middle column).name).sample index
  radiusSq := CCL.FiniteGeometric.quarterRadius
    (matrixProductErrorScale left right row column)
  radiusSq_nonneg := CCL.FiniteGeometric.quarterRadius_nonneg
    (matrixProductErrorScale_nonneg left right row column)
  later_close := by
    intro earlier later order
    let product := fun middle : Fin size =>
      CCL.TranscendentalCoherence.sampledProductApproximation
        (left row middle).name (right middle column).name
    calc
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (RFAP.ConstructiveFiniteMatrix.sumFin
              (fun middle => (product middle).sample later) -
            RFAP.ConstructiveFiniteMatrix.sumFin
              (fun middle => (product middle).sample earlier)) =
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (RFAP.ConstructiveFiniteMatrix.sumFin fun middle =>
            (product middle).sample later -
              (product middle).sample earlier) := by
          rw [RFAP.ConstructiveFiniteMatrix.sumFin_sub]
      _ <= sumBound (fun middle =>
          CCL.FiniteGeometric.quarterRadius
            (CCL.TranscendentalCoherence.sampledProductErrorScale
              (left row middle).name (right middle column).name) earlier) :=
        normSq_sumFin_le_sumBound _ _ fun middle =>
          (product middle).later_close order
      _ = CCL.FiniteGeometric.quarterRadius
          (matrixProductErrorScale left right row column) earlier :=
        sumBound_quarterRadius _ earlier
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow
      (matrixProductErrorScale left right row column) current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge
      (matrixProductErrorScale left right row column) current target
  refineIndex_accurate := CCL.FiniteGeometric.firstQuarterBelow_accurate
    (matrixProductErrorScale left right row column)
    (matrixProductErrorScale_nonneg left right row column)
  centerBound := sumBound fun middle =>
    (CCL.TranscendentalCoherence.sampledProductApproximation
      (left row middle).name (right middle column).name).centerBound
  centerBound_nonneg := sumBound_nonneg _ fun middle =>
    (CCL.TranscendentalCoherence.sampledProductApproximation
      (left row middle).name
      (right middle column).name).centerBound_nonneg
  sample_bounded := by
    intro index
    exact normSq_sumFin_le_sumBound _ _ fun middle =>
      (CCL.TranscendentalCoherence.sampledProductApproximation
        (left row middle).name
        (right middle column).name).sample_bounded index

@[simp] theorem matrixProductApproximation_sample {size : Nat}
    (left right : NamedMatrix size) (row column : Fin size) (index : Nat) :
    (matrixProductApproximation left right row column).sample index =
      RFAP.ConstructiveFiniteMatrix.sumFin fun middle =>
        (CCL.ProgressiveSampling.approximation
          (left row middle).name).sample index *
        (CCL.ProgressiveSampling.approximation
          (right middle column).name).sample index := by
  unfold matrixProductApproximation
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro middle
  exact CCL.TranscendentalCoherence.sampledProductApproximation_sample
    (left row middle).name (right middle column).name index

/-- Finite named matrix multiplication as the actual CCL arithmetic
expression tree.  The synchronization theorem below relates this tree to one
equal-index geometric sum, so normalization never assumes that unrelated
refinement levels coincide. -/
def matrixMul {size : Nat} (left right : NamedMatrix size) :
    NamedMatrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    sumNamed fun middle =>
      CCL.ProgressiveCoherence.CoherentNamed.mul
        (left row middle) (right middle column)

def scaleIdentity {size : Nat} (scalar : CoherentNamed) :
    NamedMatrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    if row = column then scalar
    else geometricNamed
      (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact 0)

@[simp] theorem matrixMul_apply {size : Nat}
    (left right : NamedMatrix size) (row column : Fin size) :
    matrixMul left right row column =
      sumNamed fun middle =>
        CCL.ProgressiveCoherence.CoherentNamed.mul
          (left row middle) (right middle column) := by
  exact RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

@[simp] theorem scaleIdentity_apply {size : Nat} (scalar : CoherentNamed)
    (row column : Fin size) :
    scaleIdentity scalar row column =
      if row = column then scalar
      else geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact 0) := by
  exact RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

/-- Entrywise operational equality of finite named matrices. -/
def MatrixEquivalent {size : Nat}
    (left right : NamedMatrix size) : Type :=
  forall row column,
    NamedEquivalent (left row column).name (right row column).name

namespace MatrixEquivalent

def refl {size : Nat} (matrix : NamedMatrix size) :
    MatrixEquivalent matrix matrix := fun row column =>
  CCL.OperationalEquivalence.NamedEquivalent.refl (matrix row column).name

def symm {size : Nat} {left right : NamedMatrix size}
    (equivalent : MatrixEquivalent left right) : MatrixEquivalent right left :=
  fun row column =>
    CCL.OperationalEquivalence.NamedEquivalent.symm
      (equivalent row column)

def trans {size : Nat} {first second third : NamedMatrix size}
    (firstSecond : MatrixEquivalent first second)
    (secondThird : MatrixEquivalent second third) :
    MatrixEquivalent first third := fun row column =>
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (firstSecond row column) (secondThird row column)

end MatrixEquivalent

/-- Transpose a finite named matrix without changing any entry process. -/
def transpose {size : Nat} (matrix : NamedMatrix size) : NamedMatrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column => matrix column row

@[simp] theorem transpose_apply {size : Nat} (matrix : NamedMatrix size)
    (row column : Fin size) :
    transpose matrix row column = matrix column row :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

/-- Transposition preserves entrywise operational equality. -/
def transpose_respects {size : Nat} {left right : NamedMatrix size}
    (equivalent : MatrixEquivalent left right) :
    MatrixEquivalent (transpose left) (transpose right) := by
  intro row column
  simpa only [transpose_apply] using equivalent column row

/-- Actual finite matrix multiplication respects entrywise operational
equality in both operands. -/
def matrixMul_respects {size : Nat}
    (leftOne leftTwo rightOne rightTwo : NamedMatrix size)
    (leftEquivalent : MatrixEquivalent leftOne leftTwo)
    (rightEquivalent : MatrixEquivalent rightOne rightTwo) :
    MatrixEquivalent (matrixMul leftOne rightOne)
      (matrixMul leftTwo rightTwo) := by
  intro row column
  rw [matrixMul_apply, matrixMul_apply]
  apply sumNamed_respects
  intro middle
  exact CCL.TranscendentalCoherence.coherentMul_respects
    (leftOne row middle) (leftTwo row middle)
    (rightOne middle column) (rightTwo middle column)
    (leftEquivalent row middle) (rightEquivalent middle column)

/-- The synchronized Gaussian matrix displayed by a named matrix at one
finite sampler index. -/
def sampledMatrix {size : Nat} (matrix : NamedMatrix size) (index : Nat) :
    RFAP.ConstructiveFiniteMatrix.Matrix Gaussian size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    (CCL.ProgressiveSampling.approximation
      (matrix row column).name).sample index

@[simp] theorem sampledMatrix_apply {size : Nat}
    (matrix : NamedMatrix size) (index : Nat) (row column : Fin size) :
    sampledMatrix matrix index row column =
      (CCL.ProgressiveSampling.approximation
        (matrix row column).name).sample index :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

/-- Replace each named entry by its canonical nested finite sampler. -/
def geometricMatrixOfNamed {size : Nat} (matrix : NamedMatrix size) :
    GeometricMatrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed
      (matrix row column).name

@[simp] theorem geometricMatrixOfNamed_apply {size : Nat}
    (matrix : NamedMatrix size) (row column : Fin size) :
    geometricMatrixOfNamed matrix row column =
      CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed
        (matrix row column).name :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

theorem sample_geometricMatrixOfNamed {size : Nat}
    (matrix : NamedMatrix size) (index : Nat) :
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
        (geometricMatrixOfNamed matrix) index =
      sampledMatrix matrix index := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply,
    geometricMatrixOfNamed_apply, sampledMatrix_apply]
  rfl

/-- The canonical synchronized division-free inverse data of a named
matrix.  This is a total finite construction; its scalar may be zero. -/
def canonicalScaledInverse {size : Nat} (matrix : NamedMatrix size) :
    CCL.Riemann.FiniteMatrixApproximation.ScaledInverseApproximation size :=
  CCL.Riemann.PivotedScaledInverse.completeApproximation
    (geometricMatrixOfNamed matrix)

/-- At each synchronized sample, the squared norm of the canonical scalar
for a one-by-one matrix is exactly the fourth power of the squared norm of
its sole entry. -/
theorem normSq_canonicalScaledInverse_one_scalar_sample
    (matrix : NamedMatrix 1) (index : Nat) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((canonicalScaledInverse matrix).scalar.sample index) =
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((CCL.ProgressiveSampling.approximation
            (matrix 0 0).name).sample index) ^ 4 := by
  rw [canonicalScaledInverse]
  rw [(CCL.Riemann.PivotedScaledInverse.completeApproximation_sample
    (geometricMatrixOfNamed matrix) index).1]
  rw [CCL.Riemann.PivotedScaledInverse.normSq_completeScaledInverse_one_scalar]
  rw [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply,
    geometricMatrixOfNamed_apply]
  rfl

/-- Canonical productive name of the fraction-free inverse scalar. -/
def canonicalInverseScalar {size : Nat} (matrix : NamedMatrix size) :
    CoherentNamed :=
  geometricNamed (canonicalScaledInverse matrix).scalar

/-- Canonical productive adjugate matrix, derived rather than supplied. -/
def canonicalAdjugate {size : Nat} (matrix : NamedMatrix size) :
    NamedMatrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    geometricNamed ((canonicalScaledInverse matrix).inverse row column)

@[simp] theorem canonicalAdjugate_apply {size : Nat}
    (matrix : NamedMatrix size) (row column : Fin size) :
    canonicalAdjugate matrix row column =
      geometricNamed ((canonicalScaledInverse matrix).inverse row column) :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

/-- A constructive fraction-free inverse certificate may apartify any
coherent scalar source operationally equivalent to the canonical
fraction-free scalar.  In particular, the source can be a certified finite
tail which omits singular coarse approximation centres. -/
structure ScaledInverseCertificate {size : Nat} (matrix : NamedMatrix size) where
  scalarSource : CoherentNamed
  sourceEquivalent : NamedEquivalent
    (canonicalInverseScalar matrix).name scalarSource.name
  scalarPossibleApart : CCL.ProgressiveCharts.PossibleApart
    scalarSource.name.process

/-- A simple synchronized-sample presentation of the remaining inverse
trust boundary.  Every quantified value is an explicit Gaussian rational at
one finite sampler index. -/
structure ScalarCandidateLowerCertificate {size : Nat}
    (matrix : NamedMatrix size) where
  lowerSq : Coordinate
  positive : 0 < lowerSq
  sample_lower : forall index,
    lowerSq <= RFAP.ConstructiveGaussian.Gaussian.normSq
      ((canonicalScaledInverse matrix).scalar.sample index)

/-- A uniform candidate lower bound for the sole entry of a one-by-one named
matrix.  This is the exact genus-one A-period nonvanishing obligation before
the pivot-complete scalar's fourth-power encoding is applied. -/
structure OneByOneEntryCandidateLowerCertificate
    (matrix : NamedMatrix 1) where
  lowerSq : Coordinate
  positive : 0 < lowerSq
  sample_lower : forall index,
    lowerSq <= RFAP.ConstructiveGaussian.Gaussian.normSq
      ((CCL.ProgressiveSampling.approximation
        (matrix 0 0).name).sample index)

namespace OneByOneEntryCandidateLowerCertificate

/-- Raise the entry lower bound to the fourth power prescribed by the exact
dimension-one pivot-complete inverse calculation. -/
def toScalarCandidateLowerCertificate {matrix : NamedMatrix 1}
    (certificate : OneByOneEntryCandidateLowerCertificate matrix) :
    ScalarCandidateLowerCertificate matrix where
  lowerSq := certificate.lowerSq ^ 4
  positive := RFAP.ConstructiveFraction.pow_pos_direct
    certificate.positive 4
  sample_lower := by
    intro index
    rw [normSq_canonicalScaledInverse_one_scalar_sample]
    exact RFAP.ConstructiveFraction.pow_le_pow_direct
      certificate.positive.le (certificate.sample_lower index) 4

end OneByOneEntryCandidateLowerCertificate

/-- A uniform positive rational projection of the sole entry of a one-by-one
matrix.  The direction is not required to be a unit vector; its exact squared
norm is retained so finite Cauchy--Schwarz can recover a norm lower bound. -/
structure OneByOneEntryDirectionalLowerCertificate
    (matrix : NamedMatrix 1) where
  direction : RFAP.ConstructiveGaussian.Gaussian
  directionNormSqPositive :
    0 < RFAP.ConstructiveGaussian.Gaussian.normSq direction
  lower : Coordinate
  positive : 0 < lower
  sample_lower : forall index,
    lower <=
      direction.re *
          ((CCL.ProgressiveSampling.approximation
            (matrix 0 0).name).sample index).re +
        direction.im *
          ((CCL.ProgressiveSampling.approximation
            (matrix 0 0).name).sample index).im

namespace OneByOneEntryDirectionalLowerCertificate

/-- A uniform oriented projection gives a uniform squared-norm lower without
choosing a square root or normalizing the displayed rational direction. -/
def toOneByOneEntryCandidateLowerCertificate {matrix : NamedMatrix 1}
    (certificate : OneByOneEntryDirectionalLowerCertificate matrix) :
    OneByOneEntryCandidateLowerCertificate matrix where
  lowerSq := certificate.lower ^ 2 /
    RFAP.ConstructiveGaussian.Gaussian.normSq certificate.direction
  positive := RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.pow_pos_direct certificate.positive 2)
    certificate.directionNormSqPositive
  sample_lower := by
    intro index
    let sample :=
      (CCL.ProgressiveSampling.approximation
        (matrix 0 0).name).sample index
    let projection :=
      certificate.direction.re * sample.re +
        certificate.direction.im * sample.im
    have lowerSqLeProjectionSq :
        certificate.lower ^ 2 <= projection ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct certificate.positive.le
        (certificate.sample_lower index) 2
    have projectionSqLe : projection ^ 2 <=
        RFAP.ConstructiveGaussian.Gaussian.normSq certificate.direction *
          RFAP.ConstructiveGaussian.Gaussian.normSq sample :=
      RFAP.ConstructiveGaussian.Gaussian.projection_sq_le_normSq_mul
        certificate.direction sample
    apply (RFAP.ConstructiveFraction.div_le_iff_pos
      certificate.directionNormSqPositive).2
    exact (lowerSqLeProjectionSq.trans projectionSqLe).trans_eq (by ring1)

end OneByOneEntryDirectionalLowerCertificate

/-- A generic tail estimate for a geometric Gaussian approximation.  One
anchor value and the approximation's built-in later-movement bound control
the squared norm of every later sample. -/
private theorem geometric_tail_normSq_lower
    (source : GeometricApproximation) {anchor index : Nat}
    (order : anchor <= index) :
    RFAP.ConstructiveGaussian.Gaussian.normSq (source.sample anchor) / 2 -
        CCL.FiniteGeometric.quarterRadius source.errorScale anchor <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (source.sample index) := by
  have movementForward := source.later_close order
  have reverseDifference :
      source.sample anchor - source.sample index =
        -(source.sample index - source.sample anchor) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.neg_re,
        RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
  have movement :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (source.sample anchor - source.sample index) <=
        CCL.FiniteGeometric.quarterRadius source.errorScale anchor := by
    rw [reverseDifference, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
    exact movementForward
  have triangle :=
    RFAP.ConstructiveGaussian.Gaussian.half_normSq_sub_le_normSq_sub
      (source.sample anchor) (source.sample index)
  apply (sub_le_iff_le_add).2
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq (source.sample anchor) / 2 <=
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (source.sample anchor - source.sample index) +
          RFAP.ConstructiveGaussian.Gaussian.normSq (source.sample index) :=
      (sub_le_iff_le_add).1 triangle
    _ <= CCL.FiniteGeometric.quarterRadius source.errorScale anchor +
        RFAP.ConstructiveGaussian.Gaussian.normSq (source.sample index) :=
      RFAP.ConstructiveFraction.add_le_add_right_direct movement _
    _ = RFAP.ConstructiveGaussian.Gaussian.normSq (source.sample index) +
        CCL.FiniteGeometric.quarterRadius source.errorScale anchor :=
      RFAP.ConstructiveFraction.add_comm _ _

/-- The geometric approximation carried by the sole entry of a one-by-one
named matrix. -/
def oneByOneEntryApproximation (matrix : NamedMatrix 1) :
    GeometricApproximation :=
  CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed
    (matrix 0 0).name

/-- A finite prefix/tail presentation of genus-one A-period separation.  All
fields are rational checks at finitely many displayed samples. -/
structure FiniteOneByOneEntrySeparationCertificate
    (matrix : NamedMatrix 1) where
  anchor : Nat
  prefixLowerSq : Coordinate
  prefixPositive : 0 < prefixLowerSq
  prefix_lower : forall index, index < anchor ->
    prefixLowerSq <= RFAP.ConstructiveGaussian.Gaussian.normSq
      ((oneByOneEntryApproximation matrix).sample index)
  tailPositive :
    0 < RFAP.ConstructiveGaussian.Gaussian.normSq
          ((oneByOneEntryApproximation matrix).sample anchor) / 2 -
        CCL.FiniteGeometric.quarterRadius
          (oneByOneEntryApproximation matrix).errorScale anchor

namespace FiniteOneByOneEntrySeparationCertificate

/-- At anchor zero the prefix is empty, so one strict rational clearance
check constructs the complete finite separation record. -/
def ofAnchorZero {matrix : NamedMatrix 1}
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
            ((oneByOneEntryApproximation matrix).sample 0) / 2 -
          CCL.FiniteGeometric.quarterRadius
            (oneByOneEntryApproximation matrix).errorScale 0) :
    FiniteOneByOneEntrySeparationCertificate matrix where
  anchor := 0
  prefixLowerSq := 1
  prefixPositive := by decide
  prefix_lower := by
    intro index before
    exact (Nat.not_lt_zero index before).elim
  tailPositive := tailPositive

/-- At anchor zero, one positive projected endpoint and one conservative
clearance check supply the complete finite entry-separation certificate.
This is the theorem-facing adapter for compact oriented cycle estimates. -/
def ofAnchorZeroDirectional {matrix : NamedMatrix 1}
    (direction : RFAP.ConstructiveGaussian.Gaussian)
    (directionNormSqPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq direction)
    (lower : Coordinate) (lowerPositive : 0 < lower)
    (projectionLower :
      lower <=
        direction.re * ((oneByOneEntryApproximation matrix).sample 0).re +
          direction.im * ((oneByOneEntryApproximation matrix).sample 0).im)
    (clearancePositive :
      0 <
        (lower ^ 2 /
          RFAP.ConstructiveGaussian.Gaussian.normSq direction) / 2 -
        CCL.FiniteGeometric.quarterRadius
          (oneByOneEntryApproximation matrix).errorScale 0) :
    FiniteOneByOneEntrySeparationCertificate matrix := by
  let sample := (oneByOneEntryApproximation matrix).sample 0
  let projection :=
    direction.re * sample.re + direction.im * sample.im
  have lowerSqLeProjectionSq : lower ^ 2 <= projection ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct lowerPositive.le
      projectionLower 2
  have projectionSqLe : projection ^ 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq direction *
        RFAP.ConstructiveGaussian.Gaussian.normSq sample :=
    RFAP.ConstructiveGaussian.Gaussian.projection_sq_le_normSq_mul
      direction sample
  have normLower :
      lower ^ 2 /
          RFAP.ConstructiveGaussian.Gaussian.normSq direction <=
        RFAP.ConstructiveGaussian.Gaussian.normSq sample := by
    apply (RFAP.ConstructiveFraction.div_le_iff_pos
      directionNormSqPositive).2
    exact (lowerSqLeProjectionSq.trans projectionSqLe).trans_eq (by ring1)
  have halfLower :
      (lower ^ 2 /
          RFAP.ConstructiveGaussian.Gaussian.normSq direction) / 2 <=
        RFAP.ConstructiveGaussian.Gaussian.normSq sample / 2 := by
    simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      normLower
      (RFAP.ConstructiveFraction.inv_pos_direct
        (by decide : (0 : Coordinate) < 2)).le
  apply ofAnchorZero
  exact clearancePositive.trans_le
    (RFAP.ConstructiveFraction.sub_le_sub_right_direct halfLower _)

def lowerSq {matrix : NamedMatrix 1}
    (certificate : FiniteOneByOneEntrySeparationCertificate matrix) :
    Coordinate :=
  min certificate.prefixLowerSq
    (RFAP.ConstructiveGaussian.Gaussian.normSq
          ((oneByOneEntryApproximation matrix).sample certificate.anchor) / 2 -
      CCL.FiniteGeometric.quarterRadius
        (oneByOneEntryApproximation matrix).errorScale certificate.anchor)

theorem lowerSq_positive {matrix : NamedMatrix 1}
    (certificate : FiniteOneByOneEntrySeparationCertificate matrix) :
    0 < certificate.lowerSq :=
  lt_min certificate.prefixPositive certificate.tailPositive

/-- Expand the finite entry check to the uniform entry lower certificate. -/
def toOneByOneEntryCandidateLowerCertificate {matrix : NamedMatrix 1}
    (certificate : FiniteOneByOneEntrySeparationCertificate matrix) :
    OneByOneEntryCandidateLowerCertificate matrix where
  lowerSq := certificate.lowerSq
  positive := certificate.lowerSq_positive
  sample_lower := by
    intro index
    change certificate.lowerSq <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        ((oneByOneEntryApproximation matrix).sample index)
    by_cases beforeAnchor : index < certificate.anchor
    · exact (min_le_left _ _).trans
        (certificate.prefix_lower index beforeAnchor)
    · exact (min_le_right _ _).trans
        (geometric_tail_normSq_lower
          (oneByOneEntryApproximation matrix)
          (Nat.le_of_not_gt beforeAnchor))

/-- The complete dimension-one inverse lower certificate follows by the
exact fourth-power scalar calculation. -/
def toScalarCandidateLowerCertificate {matrix : NamedMatrix 1}
    (certificate : FiniteOneByOneEntrySeparationCertificate matrix) :
    ScalarCandidateLowerCertificate matrix :=
  (certificate.toOneByOneEntryCandidateLowerCertificate).toScalarCandidateLowerCertificate

end FiniteOneByOneEntrySeparationCertificate

/-- Finite presentation of inverse-scalar separation.  The caller checks a
positive lower bound on the finite prefix strictly before `anchor` and one
strict rational clearance inequality at the anchor.  The displayed geometric
tail movement then supplies every later sample automatically. -/
structure FiniteScalarSeparationCertificate {size : Nat}
    (matrix : NamedMatrix size) where
  anchor : Nat
  prefixLowerSq : Coordinate
  prefixPositive : 0 < prefixLowerSq
  prefix_lower : forall index, index < anchor ->
    prefixLowerSq <= RFAP.ConstructiveGaussian.Gaussian.normSq
      ((canonicalScaledInverse matrix).scalar.sample index)
  tailPositive :
    0 < RFAP.ConstructiveGaussian.Gaussian.normSq
          ((canonicalScaledInverse matrix).scalar.sample anchor) / 2 -
        CCL.FiniteGeometric.quarterRadius
          (canonicalScaledInverse matrix).scalar.errorScale anchor

/-- Computed positive candidate for the squared norm of a finite sample
prefix.  The empty prefix uses one; a successor takes the exact rational
minimum with the newly displayed sample. -/
def finiteScalarPrefixLowerSq (source : GeometricApproximation) :
    Nat -> Coordinate
  | 0 => 1
  | count + 1 => min (finiteScalarPrefixLowerSq source count)
      (RFAP.ConstructiveGaussian.Gaussian.normSq (source.sample count))

/-- Pointwise nonvanishing of the displayed finite prefix makes its computed
rational minimum strictly positive. -/
theorem finiteScalarPrefixLowerSq_positive (source : GeometricApproximation)
    (count : Nat)
    (sampleNonzero : forall index, index < count -> source.sample index ≠ 0) :
    0 < finiteScalarPrefixLowerSq source count := by
  induction count with
  | zero =>
      change (0 : Coordinate) < 1
      decide
  | succ count inductionHypothesis =>
      unfold finiteScalarPrefixLowerSq
      apply lt_min
      · exact inductionHypothesis (fun index before =>
          sampleNonzero index (by omega0))
      · exact RFAP.ConstructiveGaussian.Gaussian.normSq_pos
          (sampleNonzero count (by omega0))

/-- The computed prefix minimum lies below every sample it contains. -/
theorem finiteScalarPrefixLowerSq_le (source : GeometricApproximation)
    {count index : Nat} (before : index < count) :
    finiteScalarPrefixLowerSq source count <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (source.sample index) := by
  induction count with
  | zero => exact (Nat.not_lt_zero index before).elim
  | succ count inductionHypothesis =>
      unfold finiteScalarPrefixLowerSq
      by_cases last : index = count
      · subst index
        exact min_le_right _ _
      · have earlier : index < count := by omega0
        exact (min_le_left _ _).trans (inductionHypothesis earlier)

namespace FiniteScalarSeparationCertificate

/-- If every synchronized scalar sample is already known to be nonzero, the
finite prefix fields are computed rather than supplied.  One checked anchor
clearance is then the only remaining separation datum. -/
def ofSampleNonzero {size : Nat} {matrix : NamedMatrix size}
    (anchor : Nat)
    (sampleNonzero : forall index,
      (canonicalScaledInverse matrix).scalar.sample index ≠ 0)
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
            ((canonicalScaledInverse matrix).scalar.sample anchor) / 2 -
          CCL.FiniteGeometric.quarterRadius
            (canonicalScaledInverse matrix).scalar.errorScale anchor) :
    FiniteScalarSeparationCertificate matrix where
  anchor := anchor
  prefixLowerSq := finiteScalarPrefixLowerSq
    (canonicalScaledInverse matrix).scalar anchor
  prefixPositive := finiteScalarPrefixLowerSq_positive
    (canonicalScaledInverse matrix).scalar anchor
      (fun index _before => sampleNonzero index)
  prefix_lower := by
    intro index before
    exact finiteScalarPrefixLowerSq_le
      (canonicalScaledInverse matrix).scalar before
  tailPositive := tailPositive

/-- Rational lower bound shared by the checked prefix and coherent tail. -/
def lowerSq {size : Nat} {matrix : NamedMatrix size}
    (certificate : FiniteScalarSeparationCertificate matrix) : Coordinate :=
  min certificate.prefixLowerSq
    (RFAP.ConstructiveGaussian.Gaussian.normSq
          ((canonicalScaledInverse matrix).scalar.sample certificate.anchor) /
        2 -
      CCL.FiniteGeometric.quarterRadius
        (canonicalScaledInverse matrix).scalar.errorScale certificate.anchor)

theorem lowerSq_positive {size : Nat} {matrix : NamedMatrix size}
    (certificate : FiniteScalarSeparationCertificate matrix) :
    0 < certificate.lowerSq :=
  lt_min certificate.prefixPositive certificate.tailPositive

private theorem tail_lower {size : Nat} {matrix : NamedMatrix size}
    (certificate : FiniteScalarSeparationCertificate matrix)
    {index : Nat} (order : certificate.anchor <= index) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
          ((canonicalScaledInverse matrix).scalar.sample certificate.anchor) /
        2 -
      CCL.FiniteGeometric.quarterRadius
          (canonicalScaledInverse matrix).scalar.errorScale
          certificate.anchor <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        ((canonicalScaledInverse matrix).scalar.sample index) := by
  exact geometric_tail_normSq_lower
    (canonicalScaledInverse matrix).scalar order

/-- The finite prefix/tail presentation expands into the established uniform
candidate lower certificate. -/
def toScalarCandidateLowerCertificate {size : Nat}
    {matrix : NamedMatrix size}
    (certificate : FiniteScalarSeparationCertificate matrix) :
    ScalarCandidateLowerCertificate matrix where
  lowerSq := certificate.lowerSq
  positive := certificate.lowerSq_positive
  sample_lower := by
    intro index
    by_cases beforeAnchor : index < certificate.anchor
    · exact (min_le_left _ _).trans
        (certificate.prefix_lower index beforeAnchor)
    · exact (min_le_right _ _).trans
        (certificate.tail_lower (Nat.le_of_not_gt beforeAnchor))

end FiniteScalarSeparationCertificate

namespace ScalarCandidateLowerCertificate

/-- Uniform finite-sample separation supplies candidate apartness; later
whole-ball apartness is derived by the ordinary apartification controller. -/
def toScaledInverseCertificate {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarCandidateLowerCertificate matrix) :
    ScaledInverseCertificate matrix where
  scalarSource := canonicalInverseScalar matrix
  sourceEquivalent := CCL.OperationalEquivalence.NamedEquivalent.refl _
  scalarPossibleApart :=
    { lowerSq := certificate.lowerSq
      positive := certificate.positive
      lower := by
        intro state value possible
        change
          (canonicalScaledInverse matrix).scalar.toApproximation.Possible
            state value at possible
        rcases possible with ⟨later, _order, rfl⟩
        exact certificate.sample_lower later }

theorem sample_scalar_nonzero {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarCandidateLowerCertificate matrix) (index : Nat) :
    (canonicalScaledInverse matrix).scalar.sample index ≠ 0 := by
  intro scalarZero
  have positiveNorm := certificate.positive.trans_le
    (certificate.sample_lower index)
  rw [scalarZero, RFAP.ConstructiveGaussian.Gaussian.normSq_zero] at positiveNorm
  exact lt_irrefl 0 positiveNorm

/-- Every synchronized finite A-matrix sample has trivial left kernel.  This
is the exact finite-dimensional nondegeneracy conclusion consumed before
normalization. -/
theorem sampledMatrix_leftKernel_trivial {size : Nat}
    {matrix : NamedMatrix size}
    (certificate : ScalarCandidateLowerCertificate matrix) (index : Nat)
    (vector : RFAP.ConstructiveFiniteMatrix.Vector Gaussian size)
    (kernel : forall row,
      RFAP.ConstructiveFiniteMatrix.matrixVector
        (sampledMatrix matrix index) vector row = 0) :
    forall row, vector row = 0 := by
  let sampled := sampledMatrix matrix index
  let computed :=
    CCL.Riemann.PivotedScaledInverse.completeScaledInverse sampled
  have scalarSample :
      (canonicalScaledInverse matrix).scalar.sample index = computed.scalar := by
    unfold canonicalScaledInverse computed sampled
    have samples :=
      CCL.Riemann.PivotedScaledInverse.completeApproximation_sample
        (geometricMatrixOfNamed matrix) index
    rw [sample_geometricMatrixOfNamed] at samples
    exact samples.1
  have scalarNonzero : computed.scalar ≠ 0 := by
    intro computedZero
    apply certificate.sample_scalar_nonzero index
    rw [scalarSample, computedZero]
  intro row
  have productZero : computed.scalar * vector row = 0 := by
    calc
      computed.scalar * vector row =
          RFAP.ConstructiveFiniteMatrix.matrixVector
            (RFAP.ConstructiveFiniteMatrix.scaleIdentity computed.scalar)
              vector row := by
        simpa only [RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using
          (RFAP.ConstructiveFiniteMatrix.vector_eq_at
            (RFAP.ConstructiveFiniteMatrix.matrixVector_scaleIdentity
              computed.scalar vector) row).symm
      _ = RFAP.ConstructiveFiniteMatrix.matrixVector
            (RFAP.ConstructiveFiniteMatrix.mul computed.inverse sampled)
              vector row := by
        rw [computed.left_identity]
      _ = RFAP.ConstructiveFiniteMatrix.matrixVector computed.inverse
            (RFAP.ConstructiveFiniteMatrix.matrixVector sampled vector) row :=
        RFAP.ConstructiveFiniteMatrix.vector_eq_at
          (RFAP.ConstructiveFiniteMatrix.matrixVector_mul
            computed.inverse sampled vector) row
      _ = 0 := by
        rw [RFAP.ConstructiveFiniteMatrix.matrixVector_apply]
        rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
          (right := fun _ => (0 : Gaussian)) (fun column => by
            rw [show RFAP.ConstructiveFiniteMatrix.matrixVector sampled
                vector column = 0 by
              exact kernel column]
            exact mul_zero _)]
        exact RFAP.ConstructiveFiniteMatrix.sumFin_zero
  by_cases vectorZero : vector row = 0
  · exact vectorZero
  · exact (RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      scalarNonzero vectorZero productZero).elim

end ScalarCandidateLowerCertificate

/-! ## Tail-only inverse separation -/

/-- The exact rational clearance tested at one proposed inverse-scalar tail
anchor.  Positivity says that the anchor centre is farther from zero than all
subsequent geometric movement allowed by the approximation. -/
def scalarTailClearanceAt {size : Nat} (matrix : NamedMatrix size)
    (anchor : Nat) : Coordinate :=
  let inverse := canonicalScaledInverse matrix
  RFAP.ConstructiveGaussian.Gaussian.normSq (inverse.scalar.sample anchor) / 2 -
    CCL.FiniteGeometric.quarterRadius
      inverse.scalar.errorScale anchor

/-- Genus-one presentation of the inverse-scalar tail clearance.  Its centre
is computed directly from the sole matrix entry; only the already-certified
inverse error scale is retained. -/
def oneByOneEntryTailClearanceAt (matrix : NamedMatrix 1)
    (anchor : Nat) : Coordinate :=
  RFAP.ConstructiveGaussian.Gaussian.normSq
      ((oneByOneEntryApproximation matrix).sample anchor) ^ 4 / 2 -
    CCL.FiniteGeometric.quarterRadius
      (canonicalScaledInverse matrix).scalar.errorScale anchor

theorem oneByOneEntryTailClearanceAt_eq_scalarTailClearanceAt
    (matrix : NamedMatrix 1) (anchor : Nat) :
    oneByOneEntryTailClearanceAt matrix anchor =
      scalarTailClearanceAt matrix anchor := by
  unfold oneByOneEntryTailClearanceAt
  dsimp only [scalarTailClearanceAt]
  rw [normSq_canonicalScaledInverse_one_scalar_sample]
  unfold oneByOneEntryApproximation
  rw [CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed_sample]

/-- One finite tail-clearance check for the canonical fraction-free inverse
scalar.  Unlike `FiniteScalarSeparationCertificate`, this record makes no
claim about the discarded prefix. -/
structure ScalarTailSeparationCertificate {size : Nat}
    (matrix : NamedMatrix size) where
  anchor : Nat
  tailPositive : 0 < scalarTailClearanceAt matrix anchor

namespace ScalarCandidateLowerCertificate

/-- A uniform scalar lower bound determines a finite tail anchor without a
search through candidate centres.  The chosen quarter-radius is already
strictly below half the certified squared-norm floor. -/
def tailAnchor {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarCandidateLowerCertificate matrix) : Nat :=
  CCL.FiniteGeometric.firstQuarterBelow
    (canonicalScaledInverse matrix).scalar.errorScale 0
      (certificate.lowerSq / 2)

/-- The canonical anchor selected from a uniform lower certificate has
strictly positive tail clearance. -/
theorem tailAnchor_clearance_positive {size : Nat}
    {matrix : NamedMatrix size}
    (certificate : ScalarCandidateLowerCertificate matrix) :
    0 < scalarTailClearanceAt matrix certificate.tailAnchor := by
  let scalar := (canonicalScaledInverse matrix).scalar
  let anchor := certificate.tailAnchor
  have halfPositive : 0 < certificate.lowerSq / 2 :=
    RFAP.ConstructiveFraction.div_pos_direct certificate.positive (by decide)
  have radiusSmall :
      CCL.FiniteGeometric.quarterRadius scalar.errorScale anchor <
        certificate.lowerSq / 2 := by
    exact CCL.FiniteGeometric.firstQuarterBelow_accurate scalar.errorScale
      scalar.errorScale_nonneg 0 (certificate.lowerSq / 2) halfPositive
  have lowerHalfLeSampleHalf :
      certificate.lowerSq / 2 <=
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (scalar.sample anchor) / 2 := by
    simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      (certificate.sample_lower anchor)
      (RFAP.ConstructiveFraction.inv_pos_direct
        (by decide : (0 : Coordinate) < 2)).le
  have radiusBelowSampleHalf :
      CCL.FiniteGeometric.quarterRadius scalar.errorScale anchor <
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (scalar.sample anchor) / 2 :=
    radiusSmall.trans_le lowerHalfLeSampleHalf
  unfold scalarTailClearanceAt
  dsimp only
  exact RFAP.ConstructiveFraction.sub_pos_direct radiusBelowSampleHalf

/-- Forget the stronger uniform separation only after selecting a certified
tail anchor.  This adapter lets tail-oriented clients share the same
apartification interface without executing a bounded scan. -/
def toScalarTailSeparationCertificate {size : Nat}
    {matrix : NamedMatrix size}
    (certificate : ScalarCandidateLowerCertificate matrix) :
    ScalarTailSeparationCertificate matrix where
  anchor := certificate.tailAnchor
  tailPositive := certificate.tailAnchor_clearance_positive

end ScalarCandidateLowerCertificate

/-- Executably test one proposed tail anchor.  The successful branch returns
the proof-bearing separation certificate produced by the same rational
comparison. -/
def scalarTailSeparationAt? {size : Nat} (matrix : NamedMatrix size)
    (anchor : Nat) : Option (ScalarTailSeparationCertificate matrix) :=
  if positive : 0 < scalarTailClearanceAt matrix anchor then
    some { anchor := anchor, tailPositive := positive }
  else none

theorem scalarTailSeparationAt?_isSome_iff {size : Nat}
    (matrix : NamedMatrix size) (anchor : Nat) :
    (scalarTailSeparationAt? matrix anchor).isSome = true ↔
      0 < scalarTailClearanceAt matrix anchor := by
  unfold scalarTailSeparationAt?
  split <;> simp_all

/-- A tail certificate found within an explicit finite search bound.  The
strict bound is retained so successful scans can be audited without replaying
the recursion. -/
structure BoundedScalarTailSeparationCertificate {size : Nat}
    (matrix : NamedMatrix size) (bound : Nat) where
  certificate : ScalarTailSeparationCertificate matrix
  anchor_lt : certificate.anchor < bound

/-- Test exactly one caller-selected anchor already known to lie in a finite
bound.  This is the direct counterpart of the newest-first prefix scan and
performs no checks at any other index. -/
def scalarTailSeparationAtWithin? {size : Nat} (matrix : NamedMatrix size)
    {bound : Nat} (anchor : Nat) (within : anchor < bound) :
    Option (BoundedScalarTailSeparationCertificate matrix bound) :=
  if positive : 0 < scalarTailClearanceAt matrix anchor then
    some
      { certificate := { anchor := anchor, tailPositive := positive }
        anchor_lt := within }
  else none

/-- Direct bounded genus-one check using the sole entry rather than a generic
sampled-matrix inversion.  The fourth-power identity transports success to
the canonical scalar certificate expected by the normalization API. -/
def oneByOneEntryTailSeparationAtWithin? (matrix : NamedMatrix 1)
    {bound : Nat} (anchor : Nat) (within : anchor < bound) :
    Option (BoundedScalarTailSeparationCertificate matrix bound) :=
  if positive : 0 < oneByOneEntryTailClearanceAt matrix anchor then
    some
      { certificate :=
          { anchor := anchor
            tailPositive := by
              rw [← oneByOneEntryTailClearanceAt_eq_scalarTailClearanceAt]
              exact positive }
        anchor_lt := within }
  else none

/-- Scan all displayed anchors below `bound`, newest first.  This is an
ordinary terminating search over exact rational inequalities; it introduces
no unbounded minimization or choice. -/
def scalarTailSeparationWithin? {size : Nat} (matrix : NamedMatrix size) :
    (bound : Nat) ->
      Option (BoundedScalarTailSeparationCertificate matrix bound)
  | 0 => none
  | bound + 1 =>
      match found : scalarTailSeparationAt? matrix bound with
      | some certificate =>
          some
            { certificate := certificate
              anchor_lt := by
                have anchorEqual : certificate.anchor = bound := by
                  unfold scalarTailSeparationAt? at found
                  split at found
                  · cases found
                    rfl
                  · contradiction
                rw [anchorEqual]
                exact Nat.lt_succ_self bound }
      | none =>
          match scalarTailSeparationWithin? matrix bound with
          | some earlier =>
              some
                { certificate := earlier.certificate
                  anchor_lt := earlier.anchor_lt.trans
                    (Nat.lt_succ_self bound) }
          | none => none

namespace ScalarTailSeparationCertificate

/-- The positive rational lower bound visible from the selected tail anchor. -/
def lowerSq {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarTailSeparationCertificate matrix) : Coordinate :=
  RFAP.ConstructiveGaussian.Gaussian.normSq
        ((canonicalScaledInverse matrix).scalar.sample certificate.anchor) / 2 -
      CCL.FiniteGeometric.quarterRadius
        (canonicalScaledInverse matrix).scalar.errorScale certificate.anchor

theorem lowerSq_positive {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarTailSeparationCertificate matrix) :
    0 < certificate.lowerSq :=
  certificate.tailPositive

/-- Every retained canonical scalar centre is nonzero.  No statement is made
about the discarded coarse prefix. -/
theorem sample_nonzero_of_anchor_le {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarTailSeparationCertificate matrix) (index : Nat)
    (order : certificate.anchor <= index) :
    (canonicalScaledInverse matrix).scalar.sample index ≠ 0 := by
  intro sampleZero
  have lower := geometric_tail_normSq_lower
    (canonicalScaledInverse matrix).scalar order
  change certificate.lowerSq <=
    RFAP.ConstructiveGaussian.Gaussian.normSq
      ((canonicalScaledInverse matrix).scalar.sample index) at lower
  rw [sampleZero, RFAP.ConstructiveGaussian.Gaussian.normSq_zero] at lower
  exact (not_lt_of_ge lower certificate.lowerSq_positive).elim

/-- Coherent scalar source obtained by deleting the uncertified finite
prefix of the canonical synchronized inverse stream. -/
def scalarSource {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarTailSeparationCertificate matrix) : CoherentNamed :=
  geometricNamed
    ((canonicalScaledInverse matrix).scalar.drop certificate.anchor)

/-- Tail deletion changes finite presentation but not operational value. -/
def sourceEquivalent {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarTailSeparationCertificate matrix) :
    NamedEquivalent (canonicalInverseScalar matrix).name
      certificate.scalarSource.name :=
  geometricNamed_drop_equivalent
    (canonicalScaledInverse matrix).scalar certificate.anchor

/-- Apartify the tail process.  Every candidate of that restricted process
is an explicitly later canonical sample, so the anchor triangle estimate
supplies the same positive lower bound without inspecting any discarded
centre. -/
def toScaledInverseCertificate {size : Nat} {matrix : NamedMatrix size}
    (certificate : ScalarTailSeparationCertificate matrix) :
    ScaledInverseCertificate matrix where
  scalarSource := certificate.scalarSource
  sourceEquivalent := certificate.sourceEquivalent
  scalarPossibleApart :=
    { lowerSq := certificate.lowerSq
      positive := certificate.lowerSq_positive
      lower := by
        intro state value possible
        change
          ((canonicalScaledInverse matrix).scalar.drop
            certificate.anchor).toApproximation.Possible state value at possible
        rcases possible with ⟨later, _order, rfl⟩
        change certificate.lowerSq <=
          RFAP.ConstructiveGaussian.Gaussian.normSq
            ((canonicalScaledInverse matrix).scalar.sample
              (certificate.anchor + later))
        exact geometric_tail_normSq_lower
          (canonicalScaledInverse matrix).scalar (by omega0) }

end ScalarTailSeparationCertificate

namespace ScaledInverseCertificate

def scalar {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.apartify
    inverse.scalarSource inverse.scalarPossibleApart

/-- The prepared scalar is uniformly apart on every displayed ball. -/
def scalarApart {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) :
    CCL.ProgressiveTransducer.Named.Apart inverse.scalar.name where
  certificate := CCL.ProgressiveCharts.apartifyApart
    inverse.scalarPossibleApart

/-- Apartification changes the finite process representation but preserves
the scalar's operational value. -/
def canonicalScalarEquivalent {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) :
    NamedEquivalent (canonicalInverseScalar matrix).name inverse.scalar.name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans inverse.sourceEquivalent
    (CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent
      inverse.scalarSource inverse.scalarPossibleApart)

def adjugate {size : Nat} {matrix : NamedMatrix size}
    (_inverse : ScaledInverseCertificate matrix) : NamedMatrix size :=
  canonicalAdjugate matrix

/-- Equal-index geometric matrix multiplication. -/
def geometricProductEntry {size : Nat}
    (left right : GeometricMatrix size) (row column : Fin size) :
    GeometricApproximation :=
  CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.sum fun middle =>
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
      (left row middle) (right middle column)

@[simp] theorem geometricProductEntry_sample {size : Nat}
    (left right : GeometricMatrix size) (row column : Fin size)
    (index : Nat) :
    (geometricProductEntry left right row column).sample index =
      RFAP.ConstructiveFiniteMatrix.mul
        (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix left index)
        (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix right index)
        row column := by
  rw [RFAP.ConstructiveFiniteMatrix.mul_apply]
  unfold geometricProductEntry
  rw [CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.sum_sample]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro middle
  simp only [CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul_sample,
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply]

/-- Matrix-level synchronized geometric product. -/
def geometricProductMatrix {size : Nat}
    (left right : GeometricMatrix size) : GeometricMatrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    geometricProductEntry left right row column

@[simp] theorem geometricProductMatrix_apply {size : Nat}
    (left right : GeometricMatrix size) (row column : Fin size) :
    geometricProductMatrix left right row column =
      geometricProductEntry left right row column :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

/-- Transpose synchronized geometric entries without resampling. -/
def geometricTranspose {size : Nat} (matrix : GeometricMatrix size) :
    GeometricMatrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column => matrix column row

@[simp] theorem geometricTranspose_apply {size : Nat}
    (matrix : GeometricMatrix size) (row column : Fin size) :
    geometricTranspose matrix row column = matrix column row :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

theorem sample_geometricProductMatrix {size : Nat}
    (left right : GeometricMatrix size) (index : Nat) :
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
        (geometricProductMatrix left right) index =
      RFAP.ConstructiveFiniteMatrix.mul
        (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix left index)
        (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix right index) := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply,
    geometricProductMatrix_apply, geometricProductEntry_sample]

/-- Transposing a synchronized product reverses its factors sample by sample. -/
theorem geometricProduct_transpose_sample {size : Nat}
    (left right : GeometricMatrix size) (row column : Fin size)
    (index : Nat) :
    (geometricProductMatrix left right column row).sample index =
      (geometricProductMatrix (geometricTranspose right)
        (geometricTranspose left) row column).sample index := by
  rw [geometricProductMatrix_apply, geometricProductMatrix_apply,
    geometricProductEntry_sample, geometricProductEntry_sample,
    RFAP.ConstructiveFiniteMatrix.mul_apply,
    RFAP.ConstructiveFiniteMatrix.mul_apply]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro middle
  simp only [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply,
    geometricTranspose_apply]
  exact RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _

/-- Wrap every synchronized geometric entry as a coherent productive name. -/
def geometricNamedMatrix {size : Nat} (matrix : GeometricMatrix size) :
    NamedMatrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    geometricNamed (matrix row column)

@[simp] theorem geometricNamedMatrix_apply {size : Nat}
    (matrix : GeometricMatrix size) (row column : Fin size) :
    geometricNamedMatrix matrix row column =
      geometricNamed (matrix row column) :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

/-- Every name is operationally equivalent to the geometric wrapper of its
canonical nested sampler. -/
def named_equivalent_geometricOfNamed (value : CoherentNamed) :
    NamedEquivalent value.name
      (geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed
          value.name)).name := by
  apply CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.TranscendentalCoherence.named_toSamplingNamed value.name)
  simpa only [geometricNamed,
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
    CCL.TranscendentalCoherence.approximationEquivalent_toNamed
      (CCL.TranscendentalCoherence.approximationEquivalentOfSamplesEq
        (CCL.ProgressiveSampling.approximation value.name)
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed
          value.name).toApproximation (by intro index; rfl))

/-- Actual finite matrix arithmetic realizes the synchronized geometric
product whenever both entry families realize their geometric sources. -/
def matrixMul_equivalent_geometricProduct {size : Nat}
    (left right : NamedMatrix size)
    (leftSource rightSource : GeometricMatrix size)
    (leftEquivalent : forall row column,
      NamedEquivalent (left row column).name
        (geometricNamed (leftSource row column)).name)
    (rightEquivalent : forall row column,
      NamedEquivalent (right row column).name
        (geometricNamed (rightSource row column)).name)
    (row column : Fin size) :
    NamedEquivalent (matrixMul left right row column).name
      (geometricNamed
        (geometricProductEntry leftSource rightSource row column)).name := by
  rw [matrixMul_apply]
  apply sumNamed_equivalent_geometricSum
  intro middle
  let leftGeometric := geometricNamed (leftSource row middle)
  let rightGeometric := geometricNamed (rightSource middle column)
  have replaceOperands : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (left row middle) (right middle column)).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        leftGeometric rightGeometric).name :=
    CCL.TranscendentalCoherence.coherentMul_respects
      (left row middle) leftGeometric
      (right middle column) rightGeometric
      (leftEquivalent row middle) (rightEquivalent middle column)
  apply CCL.OperationalEquivalence.NamedEquivalent.trans replaceOperands
  simpa only [leftGeometric, rightGeometric, geometricNamed,
    CCL.ProgressiveCoherence.CoherentNamed.mul,
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
    CCL.TranscendentalCoherence.mulToNamed_equivalent_pointwise
      (leftSource row middle).toApproximation
      (rightSource middle column).toApproximation
      (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
        (leftSource row middle) (rightSource middle column)).toApproximation
      (by intro index; rfl)

/-- Matrix-level form of the synchronized geometric realization theorem. -/
def matrixMul_equivalent_geometricProductMatrix {size : Nat}
    (left right : NamedMatrix size)
    (leftSource rightSource : GeometricMatrix size)
    (leftEquivalent : forall row column,
      NamedEquivalent (left row column).name
        (geometricNamed (leftSource row column)).name)
    (rightEquivalent : forall row column,
      NamedEquivalent (right row column).name
        (geometricNamed (rightSource row column)).name) :
    MatrixEquivalent (matrixMul left right)
      (geometricNamedMatrix
        (geometricProductMatrix leftSource rightSource)) := by
  intro row column
  rw [geometricNamedMatrix_apply,
    geometricProductMatrix_apply]
  exact matrixMul_equivalent_geometricProduct left right
    leftSource rightSource leftEquivalent rightEquivalent row column

/-- Two synchronized geometric approximations with identical finite samples
produce operationally equivalent coherent names. -/
def geometricNamed_equivalent_of_samples
    (left right : GeometricApproximation)
    (samples : forall index, left.sample index = right.sample index) :
    NamedEquivalent (geometricNamed left).name (geometricNamed right).name := by
  simpa only [geometricNamed,
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
    CCL.TranscendentalCoherence.approximationEquivalent_toNamed
      (CCL.TranscendentalCoherence.approximationEquivalentOfSamplesEq
        left.toApproximation right.toApproximation samples)

/-- Actual multiplication of two coherent names realizes any synchronized
geometric product realizing its two operands. -/
def coherentMul_equivalent_geometricMul
    (left right : CoherentNamed)
    (leftSource rightSource : GeometricApproximation)
    (leftEquivalent : NamedEquivalent left.name
      (geometricNamed leftSource).name)
    (rightEquivalent : NamedEquivalent right.name
      (geometricNamed rightSource).name) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul left right).name
      (geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
          leftSource rightSource)).name := by
  let leftGeometric := geometricNamed leftSource
  let rightGeometric := geometricNamed rightSource
  have replaceOperands : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul left right).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        leftGeometric rightGeometric).name :=
    CCL.TranscendentalCoherence.coherentMul_respects
      left leftGeometric right rightGeometric
      leftEquivalent rightEquivalent
  apply CCL.OperationalEquivalence.NamedEquivalent.trans replaceOperands
  simpa only [leftGeometric, rightGeometric, geometricNamed,
    CCL.ProgressiveCoherence.CoherentNamed.mul,
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
    CCL.TranscendentalCoherence.mulToNamed_equivalent_pointwise
      leftSource.toApproximation rightSource.toApproximation
      (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
        leftSource rightSource).toApproximation
      (by intro index; rfl)

/-- A whole named matrix is operationally its canonical synchronized sampler
matrix. -/
def matrix_equivalent_geometricOfNamed {size : Nat}
    (matrix : NamedMatrix size) :
    MatrixEquivalent matrix
      (geometricNamedMatrix (geometricMatrixOfNamed matrix)) := by
  intro row column
  rw [geometricNamedMatrix_apply, geometricMatrixOfNamed_apply]
  exact named_equivalent_geometricOfNamed (matrix row column)

/-- Associativity of synchronized geometric matrix products, exposed as
operational equality of their generated CCL matrices. -/
def geometricProductMatrix_assoc {size : Nat}
    (first second third : GeometricMatrix size) :
    MatrixEquivalent
      (geometricNamedMatrix
        (geometricProductMatrix
          (geometricProductMatrix first second) third))
      (geometricNamedMatrix
        (geometricProductMatrix first
          (geometricProductMatrix second third))) := by
  intro row column
  rw [geometricNamedMatrix_apply, geometricNamedMatrix_apply]
  apply geometricNamed_equivalent_of_samples
  intro index
  have associated :
      CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
          (geometricProductMatrix
            (geometricProductMatrix first second) third) index =
        CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
          (geometricProductMatrix first
            (geometricProductMatrix second third)) index := by
    rw [sample_geometricProductMatrix, sample_geometricProductMatrix,
      sample_geometricProductMatrix, sample_geometricProductMatrix]
    exact RFAP.ConstructiveFiniteMatrix.mul_assoc _ _ _
  simpa only [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply] using
    RFAP.ConstructiveFiniteMatrix.matrix_eq_at associated row column

/-- Actual finite CCL matrix multiplication is associative up to operational
equality.  The proof synchronizes all three inputs, applies the exact finite
Gaussian matrix theorem at every index, and returns to the arithmetic trees. -/
def matrixMul_assoc {size : Nat}
    (first second third : NamedMatrix size) :
    MatrixEquivalent (matrixMul (matrixMul first second) third)
      (matrixMul first (matrixMul second third)) := by
  let firstSource := geometricMatrixOfNamed first
  let secondSource := geometricMatrixOfNamed second
  let thirdSource := geometricMatrixOfNamed third
  let firstSecondSource :=
    geometricProductMatrix firstSource secondSource
  let secondThirdSource :=
    geometricProductMatrix secondSource thirdSource
  have firstEquivalent := matrix_equivalent_geometricOfNamed first
  have secondEquivalent := matrix_equivalent_geometricOfNamed second
  have thirdEquivalent := matrix_equivalent_geometricOfNamed third
  have firstSecondEquivalent : MatrixEquivalent
      (matrixMul first second)
      (geometricNamedMatrix firstSecondSource) := by
    exact matrixMul_equivalent_geometricProductMatrix first second
      firstSource secondSource
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          firstEquivalent row column)
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          secondEquivalent row column)
  have secondThirdEquivalent : MatrixEquivalent
      (matrixMul second third)
      (geometricNamedMatrix secondThirdSource) := by
    exact matrixMul_equivalent_geometricProductMatrix second third
      secondSource thirdSource
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          secondEquivalent row column)
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          thirdEquivalent row column)
  have leftEquivalent : MatrixEquivalent
      (matrixMul (matrixMul first second) third)
      (geometricNamedMatrix
        (geometricProductMatrix firstSecondSource thirdSource)) :=
    matrixMul_equivalent_geometricProductMatrix
      (matrixMul first second) third firstSecondSource thirdSource
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          firstSecondEquivalent row column)
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          thirdEquivalent row column)
  have rightEquivalent : MatrixEquivalent
      (matrixMul first (matrixMul second third))
      (geometricNamedMatrix
        (geometricProductMatrix firstSource secondThirdSource)) :=
    matrixMul_equivalent_geometricProductMatrix
      first (matrixMul second third) firstSource secondThirdSource
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          firstEquivalent row column)
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          secondThirdEquivalent row column)
  exact MatrixEquivalent.trans leftEquivalent
    (MatrixEquivalent.trans
      (geometricProductMatrix_assoc firstSource secondSource thirdSource)
      (MatrixEquivalent.symm rightEquivalent))

/-- Transposition reverses actual finite CCL matrix multiplication up to
operational equality. -/
def matrixMul_transpose {size : Nat} (left right : NamedMatrix size) :
    MatrixEquivalent (transpose (matrixMul left right))
      (matrixMul (transpose right) (transpose left)) := by
  let leftSource := geometricMatrixOfNamed left
  let rightSource := geometricMatrixOfNamed right
  have leftSourceEquivalent := matrix_equivalent_geometricOfNamed left
  have rightSourceEquivalent := matrix_equivalent_geometricOfNamed right
  have normalizeLeft : MatrixEquivalent
      (transpose (matrixMul left right))
      (geometricNamedMatrix
        (geometricTranspose
          (geometricProductMatrix leftSource rightSource))) := by
    intro row column
    rw [transpose_apply, geometricNamedMatrix_apply,
      geometricTranspose_apply, geometricProductMatrix_apply]
    exact matrixMul_equivalent_geometricProduct left right
      leftSource rightSource
      (fun sourceRow sourceColumn => by
        simpa only [geometricNamedMatrix_apply] using
          leftSourceEquivalent sourceRow sourceColumn)
      (fun sourceRow sourceColumn => by
        simpa only [geometricNamedMatrix_apply] using
          rightSourceEquivalent sourceRow sourceColumn)
      column row
  have transposeSamples : MatrixEquivalent
      (geometricNamedMatrix
        (geometricTranspose
          (geometricProductMatrix leftSource rightSource)))
      (geometricNamedMatrix
        (geometricProductMatrix (geometricTranspose rightSource)
          (geometricTranspose leftSource))) := by
    intro row column
    rw [geometricNamedMatrix_apply, geometricNamedMatrix_apply,
      geometricTranspose_apply]
    apply geometricNamed_equivalent_of_samples
    intro index
    exact geometricProduct_transpose_sample leftSource rightSource
      row column index
  have normalizeRight : MatrixEquivalent
      (matrixMul (transpose right) (transpose left))
      (geometricNamedMatrix
        (geometricProductMatrix (geometricTranspose rightSource)
          (geometricTranspose leftSource))) :=
    matrixMul_equivalent_geometricProductMatrix
      (transpose right) (transpose left)
      (geometricTranspose rightSource) (geometricTranspose leftSource)
      (fun row column => by
        rw [transpose_apply, geometricTranspose_apply]
        simpa only [geometricNamedMatrix_apply] using
          rightSourceEquivalent column row)
      (fun row column => by
        rw [transpose_apply, geometricTranspose_apply]
        simpa only [geometricNamedMatrix_apply] using
          leftSourceEquivalent column row)
  exact MatrixEquivalent.trans normalizeLeft
    (MatrixEquivalent.trans transposeSamples
      (MatrixEquivalent.symm normalizeRight))

/-- Multiply every matrix entry by one coherent scalar on the left. -/
def scalarMul {size : Nat} (scalar : CoherentNamed)
    (matrix : NamedMatrix size) : NamedMatrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    CCL.ProgressiveCoherence.CoherentNamed.mul scalar (matrix row column)

@[simp] theorem scalarMul_apply {size : Nat} (scalar : CoherentNamed)
    (matrix : NamedMatrix size) (row column : Fin size) :
    scalarMul scalar matrix row column =
      CCL.ProgressiveCoherence.CoherentNamed.mul scalar
        (matrix row column) :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

/-- Synchronized geometric scaled identity. -/
def geometricScaleIdentity {size : Nat}
    (scalar : GeometricApproximation) : GeometricMatrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    if row = column then scalar
    else CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact 0

@[simp] theorem geometricScaleIdentity_apply {size : Nat}
    (scalar : GeometricApproximation) (row column : Fin size) :
    geometricScaleIdentity scalar row column =
      if row = column then scalar
      else CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact 0 :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

/-- Every synchronized sample of a geometric scaled identity is the exact
finite Gaussian scaled identity. -/
theorem sample_geometricScaleIdentity {size : Nat}
    (scalar : GeometricApproximation) (index : Nat) :
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
        (geometricScaleIdentity (size := size) scalar) index =
      RFAP.ConstructiveFiniteMatrix.scaleIdentity (n := size)
        (scalar.sample index) := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply,
    geometricScaleIdentity_apply,
    RFAP.ConstructiveFiniteMatrix.scaleIdentity_apply]
  by_cases equal : row = column
  · simp only [if_pos equal]
  · simp only [if_neg equal,
      CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact_sample]

/-- The named scaled identity realizes the synchronized scaled identity of
the scalar's canonical sampler. -/
def scaleIdentity_equivalent_geometric {size : Nat}
    (scalar : CoherentNamed) :
    MatrixEquivalent (scaleIdentity (size := size) scalar)
      (geometricNamedMatrix (size := size)
        (geometricScaleIdentity (size := size)
          (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed
            scalar.name))) := by
  intro row column
  rw [scaleIdentity_apply, geometricNamedMatrix_apply,
    geometricScaleIdentity_apply]
  by_cases equal : row = column
  · simp only [if_pos equal]
    exact named_equivalent_geometricOfNamed scalar
  · simp only [if_neg equal]
    exact CCL.OperationalEquivalence.NamedEquivalent.refl _

/-- A scaled identity on the left acts by entrywise scalar multiplication at
the operational finite-request layer. -/
def scaleIdentity_mul {size : Nat} (scalar : CoherentNamed)
    (matrix : NamedMatrix size) :
    MatrixEquivalent (matrixMul (scaleIdentity scalar) matrix)
      (scalarMul scalar matrix) := by
  let scalarSource :=
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed
      scalar.name
  let identitySource : GeometricMatrix size :=
    geometricScaleIdentity scalarSource
  let matrixSource := geometricMatrixOfNamed matrix
  have normalizeProduct : MatrixEquivalent
      (matrixMul (scaleIdentity scalar) matrix)
      (geometricNamedMatrix
        (geometricProductMatrix identitySource matrixSource)) :=
    matrixMul_equivalent_geometricProductMatrix
      (scaleIdentity scalar) matrix identitySource matrixSource
      (fun row column => by
        simpa only [geometricNamedMatrix_apply,
          identitySource, scalarSource] using
          scaleIdentity_equivalent_geometric scalar row column)
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          matrix_equivalent_geometricOfNamed matrix row column)
  intro row column
  have productSamples : forall index,
      (geometricProductMatrix identitySource matrixSource row column).sample
          index =
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
          scalarSource (matrixSource row column)).sample index := by
    intro index
    calc
      (geometricProductMatrix identitySource matrixSource row column).sample
          index =
          RFAP.ConstructiveFiniteMatrix.mul
            (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
              identitySource index)
            (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
              matrixSource index) row column :=
        by
          rw [geometricProductMatrix_apply]
          exact geometricProductEntry_sample identitySource matrixSource
            row column index
      _ = scalarSource.sample index *
          (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
            matrixSource index) row column := by
        rw [show CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
              identitySource index =
              RFAP.ConstructiveFiniteMatrix.scaleIdentity
                (scalarSource.sample index) by
          exact sample_geometricScaleIdentity scalarSource index]
        simpa only [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply] using
          RFAP.ConstructiveFiniteMatrix.matrix_eq_at
            (RFAP.ConstructiveFiniteMatrix.scaleIdentity_mul
              (scalarSource.sample index)
              (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
                matrixSource index)) row column
      _ = scalarSource.sample index *
          (matrixSource row column).sample index := by
        rw [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply]
      _ = (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
          scalarSource (matrixSource row column)).sample index := rfl
  have geometricProductEquivalent : NamedEquivalent
      (geometricNamed
        (geometricProductMatrix identitySource matrixSource row column)).name
      (geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
          scalarSource (matrixSource row column))).name :=
    geometricNamed_equivalent_of_samples _ _ productSamples
  have normalizeEntry : NamedEquivalent
      (scalarMul scalar matrix row column).name
      (geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
          scalarSource (matrixSource row column))).name := by
    rw [scalarMul_apply]
    exact coherentMul_equivalent_geometricMul scalar (matrix row column)
      scalarSource (matrixSource row column)
      (by simpa only [scalarSource] using
        named_equivalent_geometricOfNamed scalar)
      (by simpa only [matrixSource, geometricMatrixOfNamed_apply] using
        named_equivalent_geometricOfNamed (matrix row column))
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (by simpa only [geometricNamedMatrix_apply,
        geometricProductMatrix_apply] using normalizeProduct row column)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (by simpa only [geometricProductMatrix_apply] using
        geometricProductEquivalent)
      (CCL.OperationalEquivalence.NamedEquivalent.symm normalizeEntry))

/-- A scaled identity on the right has the same entrywise scalar action; the
finite Gaussian commutativity step is made explicit. -/
def matrixMul_scaleIdentity {size : Nat} (matrix : NamedMatrix size)
    (scalar : CoherentNamed) :
    MatrixEquivalent (matrixMul matrix (scaleIdentity scalar))
      (scalarMul scalar matrix) := by
  let scalarSource :=
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed
      scalar.name
  let identitySource : GeometricMatrix size :=
    geometricScaleIdentity scalarSource
  let matrixSource := geometricMatrixOfNamed matrix
  have normalizeProduct : MatrixEquivalent
      (matrixMul matrix (scaleIdentity scalar))
      (geometricNamedMatrix
        (geometricProductMatrix matrixSource identitySource)) :=
    matrixMul_equivalent_geometricProductMatrix
      matrix (scaleIdentity scalar) matrixSource identitySource
      (fun row column => by
        simpa only [geometricNamedMatrix_apply] using
          matrix_equivalent_geometricOfNamed matrix row column)
      (fun row column => by
        simpa only [geometricNamedMatrix_apply,
          identitySource, scalarSource] using
          scaleIdentity_equivalent_geometric scalar row column)
  intro row column
  have productSamples : forall index,
      (geometricProductMatrix matrixSource identitySource row column).sample
          index =
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
          scalarSource (matrixSource row column)).sample index := by
    intro index
    calc
      (geometricProductMatrix matrixSource identitySource row column).sample
          index =
          RFAP.ConstructiveFiniteMatrix.mul
            (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
              matrixSource index)
            (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
              identitySource index) row column :=
        by
          rw [geometricProductMatrix_apply]
          exact geometricProductEntry_sample matrixSource identitySource
            row column index
      _ = (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
            matrixSource index) row column * scalarSource.sample index := by
        rw [show CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
              identitySource index =
              RFAP.ConstructiveFiniteMatrix.scaleIdentity
                (scalarSource.sample index) by
          exact sample_geometricScaleIdentity scalarSource index]
        simpa only [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply] using
          RFAP.ConstructiveFiniteMatrix.matrix_eq_at
            (RFAP.ConstructiveFiniteMatrix.mul_scaleIdentity
              (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
                matrixSource index) (scalarSource.sample index)) row column
      _ = (matrixSource row column).sample index * scalarSource.sample index := by
        rw [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply]
      _ = scalarSource.sample index * (matrixSource row column).sample index :=
        RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
      _ = (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
          scalarSource (matrixSource row column)).sample index := rfl
  have geometricProductEquivalent : NamedEquivalent
      (geometricNamed
        (geometricProductMatrix matrixSource identitySource row column)).name
      (geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
          scalarSource (matrixSource row column))).name :=
    geometricNamed_equivalent_of_samples _ _ productSamples
  have normalizeEntry : NamedEquivalent
      (scalarMul scalar matrix row column).name
      (geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
          scalarSource (matrixSource row column))).name := by
    rw [scalarMul_apply]
    exact coherentMul_equivalent_geometricMul scalar (matrix row column)
      scalarSource (matrixSource row column)
      (by simpa only [scalarSource] using
        named_equivalent_geometricOfNamed scalar)
      (by simpa only [matrixSource, geometricMatrixOfNamed_apply] using
        named_equivalent_geometricOfNamed (matrix row column))
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (by simpa only [geometricNamedMatrix_apply,
        geometricProductMatrix_apply] using normalizeProduct row column)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (by simpa only [geometricProductMatrix_apply] using
        geometricProductEquivalent)
      (CCL.OperationalEquivalence.NamedEquivalent.symm normalizeEntry))

/-- Transposition fixes a scaled identity operationally. -/
def transpose_scaleIdentity {size : Nat} (scalar : CoherentNamed) :
    MatrixEquivalent
      (transpose (size := size) (scaleIdentity (size := size) scalar))
      (scaleIdentity (size := size) scalar) := by
  intro row column
  rw [transpose_apply, scaleIdentity_apply, scaleIdentity_apply]
  by_cases equal : row = column
  · subst column
    exact CCL.OperationalEquivalence.NamedEquivalent.refl _
  · simp only [if_neg equal, if_neg (Ne.symm equal)]
    exact CCL.OperationalEquivalence.NamedEquivalent.refl _

/-- The synchronized left product is the canonical scaled identity at every
finite source index. -/
theorem left_geometric_sample_identity {size : Nat}
    (matrix : NamedMatrix size) (index : Nat) (row column : Fin size) :
    (geometricProductEntry (canonicalScaledInverse matrix).inverse
        (geometricMatrixOfNamed matrix) row column).sample index =
      if row = column then
        (canonicalScaledInverse matrix).scalar.sample index else 0 := by
  let source := geometricMatrixOfNamed matrix
  let computed := canonicalScaledInverse matrix
  let sampled :=
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix source index
  calc
    (geometricProductEntry computed.inverse source row column).sample index =
        RFAP.ConstructiveFiniteMatrix.mul
          (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
            computed.inverse index) sampled row column :=
      geometricProductEntry_sample computed.inverse source row column index
    _ = RFAP.ConstructiveFiniteMatrix.mul
          (CCL.Riemann.PivotedScaledInverse.completeScaledInverse
            sampled).inverse
          sampled row column := by
      rw [show CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
          computed.inverse index =
            (CCL.Riemann.PivotedScaledInverse.completeScaledInverse
              sampled).inverse by
        exact
          (CCL.Riemann.PivotedScaledInverse.completeApproximation_sample
            source index).2]
    _ = RFAP.ConstructiveFiniteMatrix.scaleIdentity
          (CCL.Riemann.PivotedScaledInverse.completeScaledInverse
            sampled).scalar
          row column :=
      RFAP.ConstructiveFiniteMatrix.matrix_eq_at
        (CCL.Riemann.PivotedScaledInverse.completeScaledInverse_left_identity
          sampled)
        row column
    _ = if row = column then
          (CCL.Riemann.PivotedScaledInverse.completeScaledInverse
            sampled).scalar else 0 :=
      RFAP.ConstructiveFiniteMatrix.scaleIdentity_apply _ row column
    _ = if row = column then computed.scalar.sample index else 0 := by
      by_cases equal : row = column
      · simp only [if_pos equal]
        exact
          (CCL.Riemann.PivotedScaledInverse.completeApproximation_sample
            source index).1.symm
      · simp only [if_neg equal]

/-- The synchronized right product satisfies the symmetric identity. -/
theorem right_geometric_sample_identity {size : Nat}
    (matrix : NamedMatrix size) (index : Nat) (row column : Fin size) :
    (geometricProductEntry (geometricMatrixOfNamed matrix)
        (canonicalScaledInverse matrix).inverse row column).sample index =
      if row = column then
        (canonicalScaledInverse matrix).scalar.sample index else 0 := by
  let source := geometricMatrixOfNamed matrix
  let computed := canonicalScaledInverse matrix
  let sampled :=
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix source index
  calc
    (geometricProductEntry source computed.inverse row column).sample index =
        RFAP.ConstructiveFiniteMatrix.mul sampled
          (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
            computed.inverse index) row column :=
      geometricProductEntry_sample source computed.inverse row column index
    _ = RFAP.ConstructiveFiniteMatrix.mul sampled
          (CCL.Riemann.PivotedScaledInverse.completeScaledInverse
            sampled).inverse
          row column := by
      rw [show CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
          computed.inverse index =
            (CCL.Riemann.PivotedScaledInverse.completeScaledInverse
              sampled).inverse by
        exact
          (CCL.Riemann.PivotedScaledInverse.completeApproximation_sample
            source index).2]
    _ = RFAP.ConstructiveFiniteMatrix.scaleIdentity
          (CCL.Riemann.PivotedScaledInverse.completeScaledInverse
            sampled).scalar
          row column :=
      RFAP.ConstructiveFiniteMatrix.matrix_eq_at
        (CCL.Riemann.PivotedScaledInverse.completeScaledInverse_right_identity
          sampled)
        row column
    _ = if row = column then
          (CCL.Riemann.PivotedScaledInverse.completeScaledInverse
            sampled).scalar else 0 :=
      RFAP.ConstructiveFiniteMatrix.scaleIdentity_apply _ row column
    _ = if row = column then computed.scalar.sample index else 0 := by
      by_cases equal : row = column
      · simp only [if_pos equal]
        exact
          (CCL.Riemann.PivotedScaledInverse.completeApproximation_sample
            source index).1.symm
      · simp only [if_neg equal]

/-- The left scaled-inverse identity for the unprepared canonical scalar is
derived from the total synchronized construction and the generic finite
Gaussian matrix theorem. -/
private def left_identity_canonical {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) (row column : Fin size) :
    NamedEquivalent (matrixMul inverse.adjugate matrix row column).name
      (scaleIdentity (canonicalInverseScalar matrix) row column).name := by
  let source := geometricMatrixOfNamed matrix
  let computed := canonicalScaledInverse matrix
  have productEquivalent : NamedEquivalent
      (matrixMul inverse.adjugate matrix row column).name
      (geometricNamed
        (geometricProductEntry computed.inverse source row column)).name :=
    matrixMul_equivalent_geometricProduct
      inverse.adjugate matrix computed.inverse source
      (fun leftRow leftColumn => by
        simpa only [adjugate, canonicalAdjugate_apply, computed,
          canonicalScaledInverse] using
          CCL.OperationalEquivalence.NamedEquivalent.refl
            (geometricNamed
              ((CCL.Riemann.PivotedScaledInverse.completeApproximation
                (geometricMatrixOfNamed matrix)).inverse
                  leftRow leftColumn)).name)
      (fun rightRow rightColumn => by
        simpa only [source, geometricMatrixOfNamed_apply] using
          named_equivalent_geometricOfNamed
            (matrix rightRow rightColumn))
      row column
  apply CCL.OperationalEquivalence.NamedEquivalent.trans productEquivalent
  by_cases equal : row = column
  · subst column
    rw [scaleIdentity_apply, if_pos rfl]
    apply geometricNamed_equivalent_of_samples
    intro index
    simpa only [if_pos] using
      left_geometric_sample_identity matrix index row row
  · rw [scaleIdentity_apply, if_neg equal]
    apply geometricNamed_equivalent_of_samples
    intro index
    have identity := left_geometric_sample_identity matrix index row column
    rw [if_neg equal] at identity
    exact identity

/-- The corresponding right identity for the unprepared scalar. -/
private def right_identity_canonical {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) (row column : Fin size) :
    NamedEquivalent (matrixMul matrix inverse.adjugate row column).name
      (scaleIdentity (canonicalInverseScalar matrix) row column).name := by
  let source := geometricMatrixOfNamed matrix
  let computed := canonicalScaledInverse matrix
  have productEquivalent : NamedEquivalent
      (matrixMul matrix inverse.adjugate row column).name
      (geometricNamed
        (geometricProductEntry source computed.inverse row column)).name :=
    matrixMul_equivalent_geometricProduct
      matrix inverse.adjugate source computed.inverse
      (fun leftRow leftColumn => by
        simpa only [source, geometricMatrixOfNamed_apply] using
          named_equivalent_geometricOfNamed
            (matrix leftRow leftColumn))
      (fun rightRow rightColumn => by
        simpa only [adjugate, canonicalAdjugate_apply, computed,
          canonicalScaledInverse] using
          CCL.OperationalEquivalence.NamedEquivalent.refl
            (geometricNamed
              ((CCL.Riemann.PivotedScaledInverse.completeApproximation
                (geometricMatrixOfNamed matrix)).inverse
                  rightRow rightColumn)).name)
      row column
  apply CCL.OperationalEquivalence.NamedEquivalent.trans productEquivalent
  by_cases equal : row = column
  · subst column
    rw [scaleIdentity_apply, if_pos rfl]
    apply geometricNamed_equivalent_of_samples
    intro index
    simpa only [if_pos] using
      right_geometric_sample_identity matrix index row row
  · rw [scaleIdentity_apply, if_neg equal]
    apply geometricNamed_equivalent_of_samples
    intro index
    have identity := right_geometric_sample_identity matrix index row column
    rw [if_neg equal] at identity
    exact identity

/-- Operational equality of scalar names lifts entrywise to their scaled
identity matrices. -/
def scaleIdentity_respects {size : Nat} (left right : CoherentNamed)
    (equivalent : NamedEquivalent left.name right.name) :
    MatrixEquivalent (scaleIdentity (size := size) left)
      (scaleIdentity (size := size) right) := by
  intro row column
  rw [scaleIdentity_apply, scaleIdentity_apply]
  by_cases equal : row = column
  · simp only [if_pos equal]
    exact equivalent
  · simp only [if_neg equal]
    exact CCL.OperationalEquivalence.NamedEquivalent.refl _

/-- Apartification preserves the left scaled-inverse identity while making
the scalar safe for productive reciprocal construction. -/
def left_identity {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) (row column : Fin size) :
    NamedEquivalent (matrixMul inverse.adjugate matrix row column).name
      (scaleIdentity inverse.scalar row column).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (left_identity_canonical inverse row column)
    (scaleIdentity_respects (size := size)
      (canonicalInverseScalar matrix) inverse.scalar
      inverse.canonicalScalarEquivalent row column)

/-- The prepared scalar likewise preserves the right scaled-inverse
identity. -/
def right_identity {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) (row column : Fin size) :
    NamedEquivalent (matrixMul matrix inverse.adjugate row column).name
      (scaleIdentity inverse.scalar row column).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (right_identity_canonical inverse row column)
    (scaleIdentity_respects (size := size)
      (canonicalInverseScalar matrix) inverse.scalar
      inverse.canonicalScalarEquivalent row column)

end ScaledInverseCertificate

/-- The one shared reciprocal of the fraction-free inverse scalar. -/
def inverseScalar {size : Nat} {matrix : NamedMatrix size}
    (inverse : ScaledInverseCertificate matrix) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.div
    (CCL.ProgressiveCoherence.CoherentNamed.exact 1)
    inverse.scalar inverse.scalarApart

/-- Construct `A^{-1}B` entrywise as `(adj(A) B) * (1 / det(A))`.
Factoring out one shared reciprocal makes operational congruence of normalized
entries a direct consequence of multiplication congruence. -/
def normalize {size : Nat} (a b : NamedMatrix size)
    (inverse : ScaledInverseCertificate a) : NamedMatrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    CCL.ProgressiveCoherence.CoherentNamed.mul
      (matrixMul inverse.adjugate b row column)
      (inverseScalar inverse)

@[simp] theorem normalize_apply {size : Nat} (a b : NamedMatrix size)
    (inverse : ScaledInverseCertificate a) (row column : Fin size) :
    normalize a b inverse row column =
      CCL.ProgressiveCoherence.CoherentNamed.mul
        (matrixMul inverse.adjugate b row column)
        (inverseScalar inverse) := by
  exact RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

/-- Period data plus the finite nondegeneracy certificate needed to construct
its normalized period matrix. -/
structure NormalizedPeriodData {genus : Nat}
    (curve : HyperellipticCurve genus) extends PeriodData curve where
  aInverse : ScaledInverseCertificate toPeriodData.aMatrix

namespace NormalizedPeriodData

/-- Form normalized period data from any operationally valid fraction-free
inverse presentation, including one obtained by certified tail deletion. -/
def ofScaledInverse {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverse : ScaledInverseCertificate data.aMatrix) :
    NormalizedPeriodData curve where
  toPeriodData := data
  aInverse := inverse

def omega {genus : Nat} {curve : HyperellipticCurve genus}
    (data : NormalizedPeriodData curve) : NamedMatrix genus :=
  normalize data.toPeriodData.aMatrix data.toPeriodData.bMatrix data.aInverse

/-- Operational symmetry is the finite constructive first bilinear relation. -/
structure SymmetryCertificate {genus : Nat}
    {curve : HyperellipticCurve genus} (data : NormalizedPeriodData curve) where
  symmetric : forall row column : Fin genus,
    NamedEquivalent (data.omega row column).name
      (data.omega column row).name

/-- Fraction-free form of the first bilinear relation after applying the
canonically derived adjugate: the numerator `adj(A) B` is operationally
symmetric. -/
structure NumeratorSymmetryCertificate {genus : Nat}
    {curve : HyperellipticCurve genus} (data : NormalizedPeriodData curve) where
  symmetric : forall row column : Fin genus,
    NamedEquivalent
      (matrixMul data.aInverse.adjugate data.toPeriodData.bMatrix
        row column).name
      (matrixMul data.aInverse.adjugate data.toPeriodData.bMatrix
        column row).name

/-- Numerator symmetry implies symmetry of the normalized period matrix by
multiplying both entries by the same persistent reciprocal scalar. -/
def symmetryOfNumerator {genus : Nat}
    {curve : HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (certificate : NumeratorSymmetryCertificate data) :
    SymmetryCertificate data where
  symmetric := by
    intro row column
    simpa only [omega, normalize_apply,
      CCL.ProgressiveCoherence.CoherentNamed.mul] using
      CCL.TranscendentalCoherence.coherentMul_respects
        (matrixMul data.aInverse.adjugate data.toPeriodData.bMatrix row column)
        (matrixMul data.aInverse.adjugate data.toPeriodData.bMatrix column row)
        (inverseScalar data.aInverse) (inverseScalar data.aInverse)
        (certificate.symmetric row column)
        (CCL.OperationalEquivalence.NamedEquivalent.refl
          (inverseScalar data.aInverse).name)

/-- One shared finite table for the normalized period matrix. -/
def omegaTable {genus : Nat} {curve : HyperellipticCurve genus}
    (data : NormalizedPeriodData curve) : CCL.ProgressiveFiniteTable.Table :=
  ⟨PeriodData.matrixChannels data.omega⟩

theorem omegaEntry_mem_table {genus : Nat}
    {curve : HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (row column : Fin genus) :
    data.omega row column ∈ data.omegaTable.channels :=
  PeriodData.matrixEntry_mem_channels data.omega row column

/-- Every normalized entry answers a finite shared-table request with its
enclosure, allowance, persistent prefix, and exact parser certificate. -/
theorem omegaEntry_sharedRequest {genus : Nat}
    {curve : HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (row column : Fin genus)
    (target : CCL.ProgressiveFiniteTable.Coordinate) (positive : 0 < target)
    (count : Nat) :
    CCL.ProgressiveFiniteTable.RequestContract data.omegaTable.channels
      (data.omega row column) target positive count :=
  data.omegaTable.member_bitstream_and_allowance
    (data.omegaEntry_mem_table row column) target positive count

def refinedOmegaEntry {genus : Nat}
    {curve : HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (target : CCL.ProgressiveFiniteTable.Coordinate) (positive : 0 < target)
    (row column : Fin genus) : CCL.ProgressiveTransducer.Named :=
  CCL.ProgressiveFiniteTable.sharedName data.omegaTable.channels
    (data.omega row column) target positive

def omegaCenter {genus : Nat} {curve : HyperellipticCurve genus}
    (data : NormalizedPeriodData curve)
    (target : CCL.ProgressiveFiniteTable.Coordinate) (positive : 0 < target)
    (row column : Fin genus) : RFAP.ConstructiveGaussian.Gaussian :=
  let entry := data.refinedOmegaEntry target positive row column
  (entry.process.ball entry.state).center

def omegaRadiusSq {genus : Nat} {curve : HyperellipticCurve genus}
    (data : NormalizedPeriodData curve)
    (target : CCL.ProgressiveFiniteTable.Coordinate) (positive : 0 < target)
    (row column : Fin genus) : CCL.ProgressiveFiniteTable.Coordinate :=
  let entry := data.refinedOmegaEntry target positive row column
  (entry.process.ball entry.state).radiusSq

theorem omegaRadiusSq_nonneg {genus : Nat}
    {curve : HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (target : CCL.ProgressiveFiniteTable.Coordinate) (positive : 0 < target)
    (row column : Fin genus) :
    0 <= data.omegaRadiusSq target positive row column := by
  unfold omegaRadiusSq
  exact ((data.refinedOmegaEntry target positive row column).process.ball
    (data.refinedOmegaEntry target positive row column).state).radiusSq_nonneg

/-- The shared finite request makes every displayed squared entry radius
strictly smaller than its rational request target. -/
theorem omegaRadiusSq_lt_target {genus : Nat}
    {curve : HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (target : CCL.ProgressiveFiniteTable.Coordinate) (positive : 0 < target)
    (row column : Fin genus) :
    data.omegaRadiusSq target positive row column < target := by
  unfold omegaRadiusSq refinedOmegaEntry
  exact CCL.ProgressiveFiniteTable.sharedName_radius_lt
    data.omegaTable.channels (data.omega row column) positive

end NormalizedPeriodData

abbrev RationalVector (size : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Vector Coordinate size
abbrev GaussianMatrix (size : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Matrix Gaussian size

/-- A displayed nonzero coordinate is the constructive witness that a finite
rational vector is nonzero. -/
structure NonzeroVector {size : Nat} (vector : RationalVector size) where
  index : Fin size
  coefficient_nonzero : vector index ≠ 0

/-- The rational imaginary quadratic form of a displayed finite matrix. -/
def imaginaryQuadraticForm {size : Nat} (vector : RationalVector size)
    (matrix : GaussianMatrix size) : Coordinate :=
  RFAP.ConstructiveFiniteMatrix.sumFin fun row =>
    RFAP.ConstructiveFiniteMatrix.sumFin fun column =>
      vector row * (matrix row column).im * vector column

/-- A finite box certificate for one requested positivity check.  It proves
the strict rational lower bound for every matrix of readings consistent with
the finitely returned CCL balls, not for an assumed completed matrix. -/
structure PositiveRequestCertificate {genus : Nat}
    {curve : HyperellipticCurve genus} (data : NormalizedPeriodData curve)
    (vector : RationalVector genus) (_nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) where
  refinementTarget : Coordinate
  refinementPositive : 0 < refinementTarget
  refinement_lt_target : refinementTarget < target
  epsilon : Coordinate
  epsilon_positive : 0 < epsilon
  compatible_positive : forall candidate : GaussianMatrix genus,
    (forall row column : Fin genus,
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (candidate row column -
            data.omegaCenter refinementTarget refinementPositive row column) <=
        data.omegaRadiusSq refinementTarget refinementPositive row column) ->
    epsilon < imaginaryQuadraticForm vector candidate

namespace PositiveRequestCertificate

/-- In particular, the finite rational centre matrix has the certified
positive lower bound. -/
theorem center_positive {genus : Nat} {curve : HyperellipticCurve genus}
    {data : NormalizedPeriodData curve} {vector : RationalVector genus}
    {nonzero : NonzeroVector vector} {target : Coordinate}
    {positive : 0 < target}
    (certificate : PositiveRequestCertificate data vector nonzero target positive) :
    certificate.epsilon < imaginaryQuadraticForm vector
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        data.omegaCenter certificate.refinementTarget
          certificate.refinementPositive row column) := by
  apply certificate.compatible_positive
  intro row column
  rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
    RFAP.ConstructiveGaussian.Gaussian.sub_self,
    RFAP.ConstructiveGaussian.Gaussian.normSq_zero]
  exact data.omegaRadiusSq_nonneg certificate.refinementTarget
    certificate.refinementPositive row column

end PositiveRequestCertificate

/-- Pointwise constructive positive-definiteness at every finite request. -/
structure PointwisePositivity {genus : Nat}
    {curve : HyperellipticCurve genus} (data : NormalizedPeriodData curve) where
  certify : forall (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target),
    PositiveRequestCertificate data vector nonzero target positive

/-- The finite constructive Riemann bilinear relations for the normalized
period matrix. -/
structure BilinearRelationsCertificate {genus : Nat}
    {curve : HyperellipticCurve genus} (data : NormalizedPeriodData curve) where
  numeratorSymmetry : NormalizedPeriodData.NumeratorSymmetryCertificate data
  positivity : PointwisePositivity data

namespace BilinearRelationsCertificate

def symmetry {genus : Nat} {curve : HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    (certificate : BilinearRelationsCertificate data) :
    NormalizedPeriodData.SymmetryCertificate data :=
  data.symmetryOfNumerator certificate.numeratorSymmetry

end BilinearRelationsCertificate

end CCL.Riemann.PeriodMatrix
