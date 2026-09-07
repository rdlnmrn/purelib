import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixStability
import CCL.Measure.PrefixProcess
import FiniteMeasure.LawCoupling

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

namespace CCL.FiniteMeasure

/-- Canonical rowwise coupling between two rational-probe pushforwards of
one finite source distribution. -/
def probeLawCoupling {ι : Type}
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (leftPoints rightPoints : ι → Proj) :
    _root_.FiniteMeasure.LawCoupling
      (distribution.map fun item => probe (leftPoints item))
      (distribution.map fun item => probe (rightPoints item)) :=
  _root_.FiniteMeasure.LawCoupling.ofMaps distribution
    (fun item => probe (leftPoints item))
    (fun item => probe (rightPoints item))

/-- Its exact transport cost is the source table's rowwise finite L1
distance. -/
theorem probeLawCoupling_transportCost {ι : Type}
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (leftPoints rightPoints : ι → Proj) :
    (probeLawCoupling distribution probe leftPoints rightPoints).transportCost
        _root_.FiniteMeasure.rationalSeparation =
      distribution.l1Distance
        (fun item => probe (leftPoints item))
        (fun item => probe (rightPoints item)) := by
  unfold probeLawCoupling
  unfold _root_.FiniteMeasure.LawCoupling.transportCost
  unfold _root_.FiniteMeasure.LawCoupling.ofMaps
  unfold _root_.FiniteMeasure.Coupling.transportCost
  rw [distribution.map_expectation]
  rfl

/-- Canonical finite law coupling between the probe pushforwards of two
realization families over the same displayed prefix table. -/
def prefixFamilyProbeLawCoupling
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate)
    (leftPoints rightPoints : CompletedPrefixCertificate → Proj) :
    _root_.FiniteMeasure.LawCoupling
      (distribution.map fun certificate => probe (leftPoints certificate))
      (distribution.map fun certificate => probe (rightPoints certificate)) :=
  probeLawCoupling distribution probe leftPoints rightPoints

/-- The canonical coupling's transport cost is exactly the finite L1
distance between the two rowwise probe observables. -/
theorem prefixFamilyProbeLawCoupling_transportCost
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate)
    (leftPoints rightPoints : CompletedPrefixCertificate → Proj) :
    (prefixFamilyProbeLawCoupling distribution probe leftPoints rightPoints
      ).transportCost _root_.FiniteMeasure.rationalSeparation =
      distribution.l1Distance
        (fun certificate => probe (leftPoints certificate))
        (fun certificate => probe (rightPoints certificate)) := by
  unfold prefixFamilyProbeLawCoupling
  exact probeLawCoupling_transportCost distribution probe leftPoints
    rightPoints

/-- CCL contraction bounds the exact expected transport cost between every
two explicitly supplied realization laws by the expected prefix radius. -/
theorem prefixFamilyProbeLawCoupling_transportCost_le
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (leftPoints rightPoints : CompletedPrefixCertificate → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (rightPoints atom.item)) :
    (prefixFamilyProbeLawCoupling distribution probe leftPoints rightPoints
      ).transportCost _root_.FiniteMeasure.rationalSeparation ≤
      distribution.expectation fun certificate =>
        factor * cylinderSpread certificate.blocks := by
  rw [prefixFamilyProbeLawCoupling_transportCost]
  exact prefixFamilyProbe_l1Distance_le distribution probe factor
    factorNonnegative sensitive leftPoints rightPoints leftRealizes
    rightRealizes

private theorem half_lt_self {target : Coordinate} (positive : 0 < target) :
    target / 2 < target := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    target = target * 1 := by ring1
    _ < target * 2 :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        positive (by decide)

/-- A computable uniform completed-block budget makes the canonical
transport cost between every two compatible realization laws smaller than
the supplied positive rational tolerance. -/
theorem prefixFamilyProbeLawCoupling_transportCost_lt_requested
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (leftPoints rightPoints : CompletedPrefixCertificate → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (rightPoints atom.item))
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredProbeBlockCount (epsilon / 2) factor ≤
        atom.item.blocks.length) :
    (prefixFamilyProbeLawCoupling distribution probe leftPoints rightPoints
      ).transportCost _root_.FiniteMeasure.rationalSeparation < epsilon := by
  have transportLe := prefixFamilyProbeLawCoupling_transportCost_le
    distribution probe factor factorPositive.le sensitive leftPoints
    rightPoints leftRealizes rightRealizes
  have radiusLeHalf : distribution.expectation (fun certificate =>
        factor * cylinderSpread certificate.blocks) ≤ epsilon / 2 := by
    calc
      distribution.expectation (fun certificate =>
            factor * cylinderSpread certificate.blocks) ≤
          distribution.expectation (fun _ => epsilon / 2) := by
        apply distribution.expectation_mono
        intro atom member
        have widthSmall := completedPrefixProbeBound_width_lt_requested
          atom.item.witness atom.item.witnessRealizes probe factor factorPositive
          sensitive (epsilon / 2)
          (RFAP.ConstructiveFraction.div_pos_direct positive (by decide))
          (enough atom member)
        have radiusNonnegative : 0 ≤
            factor * cylinderSpread atom.item.blocks :=
          RFAP.ConstructiveFraction.mul_nonneg_direct factorPositive.le
            (cylinderSpread_nonneg atom.item.blocks)
        calc
          factor * cylinderSpread atom.item.blocks ≤
              2 * (factor * cylinderSpread atom.item.blocks) := by
            calc
              _ = 0 + factor * cylinderSpread atom.item.blocks := by ring1
              _ ≤ factor * cylinderSpread atom.item.blocks +
                    factor * cylinderSpread atom.item.blocks :=
                RFAP.ConstructiveFraction.add_le_add_direct
                  radiusNonnegative le_rfl
              _ = _ := by ring1
          _ = (completedPrefixProbeBound atom.item.blocks atom.item.witness
              atom.item.witnessRealizes probe factor factorPositive.le
              sensitive).width := by
            rw [completedPrefixProbeBound_width]
          _ ≤ epsilon / 2 := widthSmall.le
      _ = epsilon / 2 := distribution.expectation_constant _
  exact transportLe.trans_lt
    (radiusLeHalf.trans_lt (half_lt_self positive))

namespace PrefixFamilyProcess

/-- At one finite process state, CCL contraction bounds the canonical
transport cost between the probe laws of every two admitted realization
families. -/
theorem probeLawCoupling_transportCost_le {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (leftPoints rightPoints : ι → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (rightPoints atom.item)) :
    (probeLawCoupling distribution probe leftPoints rightPoints).transportCost
        _root_.FiniteMeasure.rationalSeparation ≤
      distribution.expectation fun item =>
        factor * cylinderSpread (process.blocks state item) := by
  rw [CCL.FiniteMeasure.probeLawCoupling_transportCost]
  change distribution.expectation (fun item =>
      _root_.FiniteMeasure.rationalSeparation
        (probe (leftPoints item)) (probe (rightPoints item))) ≤ _
  apply distribution.expectation_mono
  intro atom member
  exact realized_probe_separation_le (leftRealizes atom member)
    (rightRealizes atom member) probe factor factorNonnegative sensitive

/-- One computed finite block request makes the canonical transport cost
between every two realization laws admitted by the returned prefixes smaller
than the supplied positive rational tolerance. -/
theorem request_probeLawCoupling_transportCost_lt {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon)
    (leftPoints rightPoints : ι → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (process.blocks
          (process.request state
            (requiredProbeBlockCount (epsilon / 2) factor)) atom.item)
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (process.blocks
          (process.request state
            (requiredProbeBlockCount (epsilon / 2) factor)) atom.item)
        (rightPoints atom.item)) :
    (probeLawCoupling distribution probe leftPoints rightPoints).transportCost
        _root_.FiniteMeasure.rationalSeparation < epsilon := by
  let requested := process.request state
    (requiredProbeBlockCount (epsilon / 2) factor)
  have transportLe := process.probeLawCoupling_transportCost_le distribution
    probe factor factorPositive.le sensitive requested leftPoints rightPoints
    leftRealizes rightRealizes
  have radiusLeHalf : distribution.expectation (fun item =>
        factor * cylinderSpread (process.blocks requested item)) ≤
      epsilon / 2 := by
    calc
      distribution.expectation (fun item =>
            factor * cylinderSpread (process.blocks requested item)) ≤
          distribution.expectation (fun _ => epsilon / 2) := by
        apply distribution.expectation_mono
        intro atom member
        have widthSmall := completedPrefixProbeBound_width_lt_requested
          (process.witness atom.item) (process.realizes requested atom.item)
          probe factor factorPositive sensitive (epsilon / 2)
          (RFAP.ConstructiveFraction.div_pos_direct positive (by decide))
          (process.request_length state
            (requiredProbeBlockCount (epsilon / 2) factor) atom.item)
        have radiusNonnegative : 0 ≤
            factor * cylinderSpread (process.blocks requested atom.item) :=
          RFAP.ConstructiveFraction.mul_nonneg_direct factorPositive.le
            (cylinderSpread_nonneg _)
        calc
          factor * cylinderSpread (process.blocks requested atom.item) ≤
              2 * (factor * cylinderSpread
                (process.blocks requested atom.item)) := by
            calc
              _ = 0 + factor * cylinderSpread
                    (process.blocks requested atom.item) := by ring1
              _ ≤ factor * cylinderSpread
                      (process.blocks requested atom.item) +
                    factor * cylinderSpread
                      (process.blocks requested atom.item) :=
                RFAP.ConstructiveFraction.add_le_add_direct
                  radiusNonnegative le_rfl
              _ = _ := by ring1
          _ = (completedPrefixProbeBound
              (process.blocks requested atom.item) (process.witness atom.item)
              (process.realizes requested atom.item) probe factor
              factorPositive.le sensitive).width := by
            rw [completedPrefixProbeBound_width]
          _ ≤ epsilon / 2 := widthSmall.le
      _ = epsilon / 2 := distribution.expectation_constant _
  exact transportLe.trans_lt
    (radiusLeHalf.trans_lt (half_lt_self positive))

end PrefixFamilyProcess

end CCL.FiniteMeasure
