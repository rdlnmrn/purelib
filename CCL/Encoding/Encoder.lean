import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.Cylinder
import mathlib.CCL.Integral
import CCL.Encoding.Normalization

/-!
# Executable choice-free CCL encoder

Algorithm 6.3 is run on an explicit uncancelled Gaussian-integer fraction.
Every search is the bounded recursive scan from `Normalization`,
and the annulus recursion decreases the displayed denominator norm.
-/

namespace CCL.Encoder

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := CCL.Integral.GaussianInt
abbrev Frac := CCL.Integral.Frac
abbrev Sector := CCL.Sectors.Sector
abbrev Proj := CCL.GaussianProjective.Proj
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev IntegralProj := CCL.Proj GaussianInt
abbrev IntegralMat2 := CCL.Mat2 GaussianInt
abbrev Word := List Bool
abbrev Block := CCL.Cylinder.Block
abbrev BlockKind := CCL.Cylinder.BlockKind
abbrev Tail := CCL.BlockContraction.Tail
abbrev CompatibleTail := CCL.BlockContraction.CompatibleTail
abbrev ProjectiveTail := CCL.Cylinder.ProjectiveTail
abbrev ProjectiveRealizes := CCL.Cylinder.ProjectiveRealizes

open CCL.Integral
open CCL.Integral.GaussianInt
open CCL.Sectors
open CCL.Cylinder

/-- Identify a finite Gaussian-integer fraction from a proposed value by one
cross-multiplication.  This avoids evaluating a quotient when a small exact
coordinate is already known. -/
theorem Frac.value_eq_of_mul_den (fraction : Frac) (candidate : Gaussian)
    (identity : candidate * toGaussian fraction.den =
      toGaussian fraction.num) :
    fraction.value = candidate := by
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    fraction.den_toGaussian_ne
  rw [fraction.value_mul_den]
  exact identity.symm

/-- Integral version of the low-header matrix. -/
def lowScaleInt (exponent : Nat) : IntegralMat2 :=
  ⟨1, 0, 0, natPow gammaInt exponent⟩

/-- Integral sector subtraction followed by `γ`-inversion. -/
def sectorMatrixInt (sector : Sector) : IntegralMat2 :=
  CCL.Mat2.mul (CCL.Mat2.translate (sectorInt sector))
    (CCL.Mat2.invert gammaInt)

/-- Integral completed regular block. -/
def regularBlockInt (exponent : Nat) (sector : Sector) : IntegralMat2 :=
  CCL.Mat2.mul (CCL.Mat2.scale (natPow gammaInt exponent))
    (sectorMatrixInt sector)

/-- Integral completed initial-low block. -/
def lowBlockInt (exponent : Nat) (sector : Sector) : IntegralMat2 :=
  CCL.Mat2.mul (lowScaleInt exponent) (sectorMatrixInt sector)

/-- Coordinatewise embedding of an integral projective pair. -/
def mapProj (point : IntegralProj) : Proj :=
  ⟨toGaussian point.p, toGaussian point.q⟩

/-- Coordinatewise embedding of an integral decoder matrix. -/
def mapMat (matrix : IntegralMat2) : Mat2 :=
  ⟨toGaussian matrix.a, toGaussian matrix.b,
    toGaussian matrix.c, toGaussian matrix.d⟩

@[simp] theorem mapProj_omega :
    mapProj (CCL.Proj.omega : IntegralProj) = (CCL.Proj.omega : Proj) := rfl

@[simp] theorem mapProj_act (matrix : IntegralMat2) (point : IntegralProj) :
    mapProj (CCL.Mat2.act matrix point) =
      CCL.Mat2.act (mapMat matrix) (mapProj point) := by
  ext <;> simp only [mapProj, mapMat, CCL.Mat2.act,
    toGaussian_add, toGaussian_mul]

theorem mapProj_equivalent {left right : IntegralProj}
    (equivalent : CCL.Proj.Equivalent left right) :
    CCL.Proj.Equivalent (mapProj left) (mapProj right) := by
  dsimp only [CCL.Proj.Equivalent, mapProj] at equivalent ⊢
  simpa only [toGaussian_mul] using congrArg toGaussian equivalent

theorem map_regularBlockInt (exponent : Nat) (sector : Sector) :
    mapMat (regularBlockInt exponent sector) =
      CCL.Decoder.regularBlock exponent sector := by
  apply CCL.Mat2.ext <;>
    simp only [mapMat, regularBlockInt, sectorMatrixInt,
      CCL.Decoder.regularBlock, CCL.Mat2.mul, CCL.Mat2.scale,
      CCL.Mat2.translate, CCL.Mat2.invert, toGaussian_add,
      toGaussian_mul, toGaussian_zero, toGaussian_one,
      toGaussian_gammaInt_pow, toGaussian_gammaInt,
      toGaussian_sectorInt,
      RFAP.ConstructiveGaussian.Gaussian.natPow_succ] <;>
    ring1

theorem map_lowBlockInt (exponent : Nat) (sector : Sector) :
    mapMat (lowBlockInt exponent sector) =
      CCL.Decoder.lowBlock exponent sector := by
  apply CCL.Mat2.ext <;>
    simp only [mapMat, lowBlockInt, lowScaleInt, sectorMatrixInt,
      CCL.Decoder.lowBlock, CCL.Mat2.mul,
      CCL.Mat2.translate, CCL.Mat2.invert, toGaussian_add,
      toGaussian_mul, toGaussian_zero, toGaussian_one,
      toGaussian_gammaInt_pow, toGaussian_gammaInt,
      toGaussian_sectorInt,
      RFAP.ConstructiveGaussian.Gaussian.natPow_succ] <;>
    ring1

/-- A fraction certified to lie in the closed CCL band. -/
structure Annulus where
  frac : Frac
  band : Sector.Band frac.value

private theorem frac_entry_of_bounds (fraction : Frac)
    (lower : normNat fraction.den ≤ normNat fraction.num)
    (upper : normNat fraction.num < 2 * normNat fraction.den) :
    Sector.Entry fraction.value := by
  rw [Sector.Entry, Frac.normSq_value]
  have denominatorPositive :
      (0 : Coordinate) < (normNat fraction.den : Nat) :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (normNat_pos fraction.den_ne)
  constructor
  · apply (RFAP.ConstructiveFraction.le_div_iff_pos denominatorPositive).2
    rw [RFAP.ConstructiveFraction.one_mul]
    exact RFAP.ConstructiveFraction.natCast_le_direct lower
  · apply (RFAP.ConstructiveFraction.div_lt_iff_pos denominatorPositive).2
    have castUpper := RFAP.ConstructiveFraction.natCast_lt_direct upper
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using castUpper

private theorem frac_loop_of_bounds (fraction : Frac)
    (lower : normNat fraction.den < normNat fraction.num)
    (upper : normNat fraction.num ≤ 2 * normNat fraction.den) :
    Sector.Loop fraction.value := by
  rw [Sector.Loop, Frac.normSq_value]
  have denominatorPositive :
      (0 : Coordinate) < (normNat fraction.den : Nat) :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (normNat_pos fraction.den_ne)
  constructor
  · apply (RFAP.ConstructiveFraction.lt_div_iff_pos denominatorPositive).2
    rw [RFAP.ConstructiveFraction.one_mul]
    exact RFAP.ConstructiveFraction.natCast_lt_direct lower
  · apply (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).2
    have castUpper := RFAP.ConstructiveFraction.natCast_le_direct upper
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using castUpper

private theorem entry_band {value : Gaussian} (entry : Sector.Entry value) :
    Sector.Band value := ⟨entry.1, entry.2.le⟩

private theorem loop_band {value : Gaussian} (loop : Sector.Loop value) :
    Sector.Band value := ⟨loop.1.le, loop.2⟩

/-- Initial normalization and its exact integral reconstruction data. -/
structure InitialResult (fraction : Frac) where
  header : Word
  radial : IntegralMat2
  annulus : Annulus
  radial_reconstruct :
    CCL.Proj.Equivalent
      (CCL.Mat2.act radial
        ⟨annulus.frac.num, annulus.frac.den⟩)
      ⟨fraction.num, fraction.den⟩
  radial_den_ne :
    (CCL.Mat2.act radial
      ⟨annulus.frac.num, annulus.frac.den⟩).q ≠ 0

/-- Initial high branch `1ᵏ0`. -/
def initialHigh (fraction : Frac) (_numeratorNonzero : fraction.num ≠ 0)
    (highBranch : 2 * normNat fraction.den ≤ normNat fraction.num) :
    InitialResult fraction := by
  let scan := CCL.Normalization.high
    (normNat fraction.num) (normNat fraction.den)
    (normNat_pos fraction.den_ne) highBranch
  let denominator := natPow gammaInt scan.exponent * fraction.den
  have denominatorNonzero : denominator ≠ 0 :=
    GaussianInt.mul_ne_zero
      (natPow_ne_zero gammaInt (by decide) scan.exponent)
      fraction.den_ne
  let normalized : Frac := ⟨fraction.num, denominator, denominatorNonzero⟩
  have denominatorNorm :
      normNat denominator = 2 ^ scan.exponent * normNat fraction.den := by
    simp only [denominator, normNat_mul, normNat_gammaInt_pow]
  have lower : normNat normalized.den ≤ normNat normalized.num := by
    dsimp only [normalized]
    rw [denominatorNorm]
    exact scan.lower
  have upper : normNat normalized.num < 2 * normNat normalized.den := by
    dsimp only [normalized]
    rw [denominatorNorm]
    calc
      normNat fraction.num <
          2 ^ (scan.exponent + 1) * normNat fraction.den := scan.upper
      _ = 2 * (2 ^ scan.exponent * normNat fraction.den) := by
        rw [Nat.pow_succ]
        simp only [Nat.mul_comm, Nat.mul_left_comm]
  let entry := frac_entry_of_bounds normalized lower upper
  refine
    ⟨List.replicate scan.exponent true ++ [false],
      CCL.Mat2.scale (natPow gammaInt scan.exponent),
      ⟨normalized, entry_band entry⟩, ?_, ?_⟩
  · dsimp only [normalized, denominator, CCL.Proj.Equivalent,
      CCL.Mat2.act, CCL.Mat2.scale]
    ring1
  · dsimp only [normalized, CCL.Mat2.act, CCL.Mat2.scale]
    simpa only [zero_add, one_mul, zero_mul] using denominatorNonzero

/-- Initial low branch `01ᵐ0`. -/
def initialLow (fraction : Frac) (numeratorNonzero : fraction.num ≠ 0)
    (lowBranch : normNat fraction.num < 2 * normNat fraction.den) :
    InitialResult fraction := by
  let scan := CCL.Normalization.low
    (normNat fraction.num) (normNat fraction.den)
    (normNat_pos numeratorNonzero) (normNat_pos fraction.den_ne) lowBranch
  let numerator := natPow gammaInt scan.exponent * fraction.num
  let normalized : Frac := ⟨numerator, fraction.den, fraction.den_ne⟩
  have numeratorNorm :
      normNat numerator = 2 ^ scan.exponent * normNat fraction.num := by
    simp only [numerator, normNat_mul, normNat_gammaInt_pow]
  have lower : normNat normalized.den ≤ normNat normalized.num := by
    dsimp only [normalized]
    rw [numeratorNorm]
    exact scan.lower
  have upper : normNat normalized.num < 2 * normNat normalized.den := by
    dsimp only [normalized]
    rw [numeratorNorm]
    exact scan.upper
  let entry := frac_entry_of_bounds normalized lower upper
  refine
    ⟨false :: List.replicate scan.exponent true ++ [false],
      lowScaleInt scan.exponent,
      ⟨normalized, entry_band entry⟩, ?_, ?_⟩
  · dsimp only [normalized, numerator, lowScaleInt,
      CCL.Proj.Equivalent, CCL.Mat2.act]
    ring1
  · dsimp only [normalized, lowScaleInt, CCL.Mat2.act]
    simpa only [zero_mul, zero_add] using GaussianInt.mul_ne_zero
      (natPow_ne_zero gammaInt (by decide) scan.exponent) fraction.den_ne

/-- The finite state immediately after sector subtraction and inversion. -/
structure PostInversion (old : Annulus) where
  frac : Frac
  num_eq : frac.num = old.frac.den
  den_eq : frac.den = gammaInt *
    (old.frac.num - sectorInt (Sector.select old.frac.value) * old.frac.den)
  den_descent : normNat frac.den < normNat old.frac.den

/-- One nonterminal sector step, with direct natural-norm descent. -/
def postInversion (old : Annulus)
    (residualNonzero :
      old.frac.num - sectorInt (Sector.select old.frac.value) *
        old.frac.den ≠ 0) : PostInversion old := by
  let sector := Sector.select old.frac.value
  let residual := old.frac.num - sectorInt sector * old.frac.den
  have residualNonzero' : residual ≠ 0 := by
    simpa only [residual, sector] using residualNonzero
  let denominator := gammaInt * residual
  have denominatorNonzero : denominator ≠ 0 :=
    GaussianInt.mul_ne_zero (by decide) residualNonzero'
  let next : Frac := ⟨old.frac.den, denominator, denominatorNonzero⟩
  have descent := CCL.Decoder.inversion_stage_descent
    old.frac.den_toGaussian_ne old.band sector
    (Sector.select_spec old.frac.value old.band.1)
    old.frac.value_mul_den.symm
  have denominatorMap : toGaussian denominator =
      RFAP.ConstructiveGaussian.Gaussian.gamma *
        (toGaussian old.frac.num - sector.rep *
          toGaussian old.frac.den) := by
    simp only [denominator, residual, toGaussian_mul, toGaussian_sub,
      toGaussian_gammaInt, toGaussian_sectorInt]
  rw [← denominatorMap, normSq_toGaussian, normSq_toGaussian] at descent
  exact
    ⟨next, rfl, rfl,
      RFAP.ConstructiveFraction.natCast_lt_iff_direct.mp descent⟩

/-- Loop normalization and its strict recursive-call measure. -/
structure LoopResult (post : Frac) (oldMeasure : Nat) where
  exponent : Nat
  annulus : Annulus
  num_eq : annulus.frac.num = post.num
  den_eq : annulus.frac.den = natPow gammaInt exponent * post.den
  measure_lt : normNat annulus.frac.den < oldMeasure

/-- Normalize a post-inversion state back into the half-open loop band. -/
def normalizeLoop (post : Frac) (oldMeasure : Nat)
    (postStrict : normNat post.den < normNat post.num)
    (numeratorMeasure : normNat post.num = oldMeasure) :
    LoopResult post oldMeasure := by
  let scan := CCL.Normalization.loop
    (normNat post.num) (normNat post.den)
    (normNat_pos post.den_ne) postStrict
  let denominator := natPow gammaInt scan.exponent * post.den
  have denominatorNonzero : denominator ≠ 0 :=
    GaussianInt.mul_ne_zero
      (natPow_ne_zero gammaInt (by decide) scan.exponent) post.den_ne
  let normalized : Frac := ⟨post.num, denominator, denominatorNonzero⟩
  have denominatorNorm :
      normNat denominator = 2 ^ scan.exponent * normNat post.den := by
    simp only [denominator, normNat_mul, normNat_gammaInt_pow]
  have lower : normNat normalized.den < normNat normalized.num := by
    dsimp only [normalized]
    rw [denominatorNorm]
    exact scan.lower
  have upper : normNat normalized.num ≤ 2 * normNat normalized.den := by
    dsimp only [normalized]
    rw [denominatorNorm]
    calc
      normNat post.num ≤
          2 ^ (scan.exponent + 1) * normNat post.den := scan.upper
      _ = 2 * (2 ^ scan.exponent * normNat post.den) := by
        rw [Nat.pow_succ]
        simp only [Nat.mul_comm, Nat.mul_left_comm]
  let loop := frac_loop_of_bounds normalized lower upper
  refine ⟨scan.exponent, ⟨normalized, loop_band loop⟩, rfl, rfl, ?_⟩
  calc
    normNat normalized.den < normNat normalized.num := lower
    _ = normNat post.num := rfl
    _ = oldMeasure := numeratorMeasure

/-! ## Completed-block realization data -/

private theorem terminal_value_eq_rep (annulus : Annulus) (sector : Sector)
    (residualZero :
      annulus.frac.num - sectorInt sector * annulus.frac.den = 0) :
    annulus.frac.value = sector.rep := by
  have numeratorIdentity :
      annulus.frac.num = sectorInt sector * annulus.frac.den :=
    sub_eq_zero.mp residualZero
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    annulus.frac.den_toGaussian_ne
  calc
    annulus.frac.value * toGaussian annulus.frac.den =
        toGaussian annulus.frac.num := annulus.frac.value_mul_den
    _ = toGaussian (sectorInt sector * annulus.frac.den) := by
      rw [numeratorIdentity]
    _ = sector.rep * toGaussian annulus.frac.den := by
      rw [toGaussian_mul, toGaussian_sectorInt]

private theorem post_compatible (annulus : Annulus)
    (post : PostInversion annulus) :
    CompatibleTail (Sector.select annulus.frac.value)
      post.frac.value annulus.frac.value := by
  let sector := Sector.select annulus.frac.value
  have postNumerator : toGaussian post.frac.num =
      toGaussian annulus.frac.den := by rw [post.num_eq]
  have postDenominator : toGaussian post.frac.den =
      RFAP.ConstructiveGaussian.Gaussian.gamma *
        (toGaussian annulus.frac.num - sector.rep *
          toGaussian annulus.frac.den) := by
    rw [post.den_eq]
    simp only [sector, toGaussian_mul, toGaussian_sub,
      toGaussian_gammaInt, toGaussian_sectorInt]
  have leftScaled :
      (RFAP.ConstructiveGaussian.Gaussian.gamma * post.frac.value *
          annulus.frac.value) * toGaussian post.frac.den =
        RFAP.ConstructiveGaussian.Gaussian.gamma *
          toGaussian annulus.frac.num := by
    calc
      (RFAP.ConstructiveGaussian.Gaussian.gamma * post.frac.value *
          annulus.frac.value) * toGaussian post.frac.den =
          RFAP.ConstructiveGaussian.Gaussian.gamma *
            (post.frac.value * toGaussian post.frac.den) *
              annulus.frac.value := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
          ring1
      _ = RFAP.ConstructiveGaussian.Gaussian.gamma *
          toGaussian post.frac.num * annulus.frac.value := by
        rw [post.frac.value_mul_den]
      _ = RFAP.ConstructiveGaussian.Gaussian.gamma *
          toGaussian annulus.frac.den * annulus.frac.value := by
        rw [postNumerator]
      _ = RFAP.ConstructiveGaussian.Gaussian.gamma *
          (annulus.frac.value * toGaussian annulus.frac.den) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
          ring1
      _ = RFAP.ConstructiveGaussian.Gaussian.gamma *
          toGaussian annulus.frac.num := by
        rw [annulus.frac.value_mul_den]
  have rightScaled :
      (RFAP.ConstructiveGaussian.Gaussian.gamma * post.frac.value *
          sector.rep + 1) * toGaussian post.frac.den =
        RFAP.ConstructiveGaussian.Gaussian.gamma *
          toGaussian annulus.frac.num := by
    calc
      (RFAP.ConstructiveGaussian.Gaussian.gamma * post.frac.value *
          sector.rep + 1) * toGaussian post.frac.den =
          RFAP.ConstructiveGaussian.Gaussian.gamma *
              (post.frac.value * toGaussian post.frac.den) * sector.rep +
            toGaussian post.frac.den := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im,
            RFAP.ConstructiveGaussian.Gaussian.one_re,
            RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
          ring1
      _ = RFAP.ConstructiveGaussian.Gaussian.gamma *
          toGaussian post.frac.num * sector.rep +
            toGaussian post.frac.den := by
        rw [post.frac.value_mul_den]
      _ = RFAP.ConstructiveGaussian.Gaussian.gamma *
          toGaussian annulus.frac.den * sector.rep +
            toGaussian post.frac.den := by
        rw [postNumerator]
      _ = RFAP.ConstructiveGaussian.Gaussian.gamma *
          toGaussian annulus.frac.den * sector.rep +
            RFAP.ConstructiveGaussian.Gaussian.gamma *
              (toGaussian annulus.frac.num - sector.rep *
                toGaussian annulus.frac.den) := by
        rw [postDenominator]
      _ = RFAP.ConstructiveGaussian.Gaussian.gamma *
          toGaussian annulus.frac.num := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
          ring1
  refine
    { equation := ?_
      band := annulus.band
      holds := Sector.select_spec annulus.frac.value annulus.band.1 }
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    post.frac.den_toGaussian_ne
  exact leftScaled.trans rightScaled.symm

private theorem value_of_scaled_den
    (source normalized : Frac) (exponent : Nat)
    (numeratorIdentity : normalized.num = source.num)
    (denominatorIdentity : normalized.den =
      natPow gammaInt exponent * source.den) :
    RFAP.ConstructiveGaussian.Gaussian.natPow
        RFAP.ConstructiveGaussian.Gaussian.gamma exponent *
      normalized.value = source.value := by
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    source.den_toGaussian_ne
  calc
    (RFAP.ConstructiveGaussian.Gaussian.natPow
          RFAP.ConstructiveGaussian.Gaussian.gamma exponent *
        normalized.value) * toGaussian source.den =
        normalized.value *
          (RFAP.ConstructiveGaussian.Gaussian.natPow
            RFAP.ConstructiveGaussian.Gaussian.gamma exponent *
              toGaussian source.den) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1
    _ = normalized.value * toGaussian normalized.den := by
      rw [denominatorIdentity, toGaussian_mul, toGaussian_gammaInt_pow]
    _ = toGaussian normalized.num := normalized.value_mul_den
    _ = toGaussian source.num := by rw [numeratorIdentity]
    _ = source.value * toGaussian source.den :=
      source.value_mul_den.symm

private theorem value_of_scaled_num
    (source normalized : Frac) (exponent : Nat)
    (numeratorIdentity : normalized.num =
      natPow gammaInt exponent * source.num)
    (denominatorIdentity : normalized.den = source.den) :
    normalized.value =
      RFAP.ConstructiveGaussian.Gaussian.natPow
        RFAP.ConstructiveGaussian.Gaussian.gamma exponent * source.value := by
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    source.den_toGaussian_ne
  calc
    normalized.value * toGaussian source.den =
        normalized.value * toGaussian normalized.den := by
      rw [denominatorIdentity]
    _ = toGaussian normalized.num := normalized.value_mul_den
    _ = toGaussian (natPow gammaInt exponent * source.num) := by
      rw [numeratorIdentity]
    _ = RFAP.ConstructiveGaussian.Gaussian.natPow
          RFAP.ConstructiveGaussian.Gaussian.gamma exponent *
        toGaussian source.num := by
      rw [toGaussian_mul, toGaussian_gammaInt_pow]
    _ = RFAP.ConstructiveGaussian.Gaussian.natPow
          RFAP.ConstructiveGaussian.Gaussian.gamma exponent *
        (source.value * toGaussian source.den) := by
      rw [source.value_mul_den]
    _ = (RFAP.ConstructiveGaussian.Gaussian.natPow
          RFAP.ConstructiveGaussian.Gaussian.gamma exponent * source.value) *
        toGaussian source.den := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1

private theorem normalized_scaled_value (post : Frac) (oldMeasure : Nat)
    (postStrict : normNat post.den < normNat post.num)
    (numeratorMeasure : normNat post.num = oldMeasure) :
    RFAP.ConstructiveGaussian.Gaussian.natPow
        RFAP.ConstructiveGaussian.Gaussian.gamma
        (normalizeLoop post oldMeasure postStrict numeratorMeasure).exponent *
      (normalizeLoop post oldMeasure postStrict numeratorMeasure).annulus.frac.value =
        post.value := by
  let normalized := normalizeLoop post oldMeasure postStrict numeratorMeasure
  exact value_of_scaled_den post normalized.annulus.frac normalized.exponent
    normalized.num_eq normalized.den_eq

/-- Recursive completed-block data beginning immediately after the current
annulus sector code. -/
structure AnnulusBlockEncoding (annulus : Annulus) where
  continuation : List Block
  tail : ProjectiveTail (Sector.select annulus.frac.value)
  realizes : ProjectiveRealizes continuation tail.point
  models : tail.model.ModelsValue annulus.frac.value

/-- Fuel-bounded structural form of the annulus encoder.  The bound is a
certificate that the strictly decreasing denominator norm cannot exhaust the
supplied fuel. -/
private def encodeAnnulusBlocksFuel :
    (fuel : Nat) → (annulus : Annulus) →
      normNat annulus.frac.den < fuel → AnnulusBlockEncoding annulus
  | 0, annulus, bound => False.elim (Nat.not_lt_zero _ bound)
  | fuel + 1, annulus, bound =>
      if slack : normNat annulus.frac.den < fuel then
        encodeAnnulusBlocksFuel fuel annulus slack
      else
        let sector := Sector.select annulus.frac.value
        let residual :=
          annulus.frac.num - sectorInt sector * annulus.frac.den
        if residualZero : residual = 0 then
          let model : Tail sector := .omega
          let tail := ProjectiveTail.ofTail model
          ⟨[], tail,
            ProjectiveRealizes.done tail.point tail.valid,
            by
              change annulus.frac.value = sector.rep
              exact terminal_value_eq_rep annulus sector (by
                simpa only [residual, sector] using residualZero)⟩
        else
          let post := postInversion annulus (by
            simpa only [residual, sector] using residualZero)
          let normalized := normalizeLoop post.frac (normNat annulus.frac.den)
            post.den_descent rfl
          have measureEq : normNat annulus.frac.den = fuel :=
            Nat.le_antisymm (Nat.le_of_lt_succ bound) (Nat.le_of_not_gt slack)
          let next := encodeAnnulusBlocksFuel fuel normalized.annulus (by
            simpa only [measureEq] using normalized.measure_lt)
          let block : Block :=
            ⟨.regular, normalized.exponent,
              Sector.select normalized.annulus.frac.value⟩
          let model : Tail sector :=
            .affine post.frac.value annulus.frac.value
              (post_compatible annulus post)
          let point := CCL.Mat2.act block.matrix next.tail.point
          let tail : ProjectiveTail sector :=
            { point := point
              valid := block.act_projectiveTail_valid next.tail
              model := model
              equivalent := by
                have acted : point.Equivalent
                    (CCL.Mat2.act block.matrix next.tail.model.point) :=
                  CCL.Mat2.act_respects_equivalent block.matrix
                    next.tail.equivalent
                have modeled :
                    (CCL.Mat2.act block.matrix next.tail.model.point).Equivalent
                      (CCL.Proj.affine post.frac.value) := by
                  dsimp only [block, CCL.Cylinder.Block.matrix]
                  exact CCL.Cylinder.Tail.regularBlock_act_equivalent
                    normalized.exponent next.tail.model
                    normalized.annulus.frac.value post.frac.value next.models
                    (normalized_scaled_value post.frac
                      (normNat annulus.frac.den) post.den_descent rfl)
                exact CCL.Chordal.Proj.equivalent_trans acted modeled
                  (block.act_model_valid next.tail)
                  (CCL.Chordal.Proj.affine_hasNonzeroCoordinate
                    post.frac.value) }
          ⟨block :: next.continuation, tail,
            ProjectiveRealizes.step block next.tail next.realizes,
            rfl⟩

/-- The terminating encoder produces an exact projectively rescaled
completed-block realization, not merely a raw bit word. -/
def encodeAnnulusBlocks (annulus : Annulus) : AnnulusBlockEncoding annulus :=
  encodeAnnulusBlocksFuel (Nat.succ (normNat annulus.frac.den)) annulus
    (Nat.lt_succ_self _)

private theorem encodeAnnulusBlocksFuel_continuation_of_eq
    (annulus : Annulus)
    (residualZero :
      annulus.frac.num -
          sectorInt (Sector.select annulus.frac.value) * annulus.frac.den =
        0) :
    (encodeAnnulusBlocksFuel (Nat.succ (normNat annulus.frac.den)) annulus
      (Nat.lt_succ_self _)).continuation = [] := by
  rw [encodeAnnulusBlocksFuel]
  simp only [dif_neg (Nat.lt_irrefl _), dif_pos residualZero]

private theorem encodeAnnulusBlocksFuel_continuation_of_ne
    (annulus : Annulus)
    (residualNonzero :
      annulus.frac.num -
          sectorInt (Sector.select annulus.frac.value) * annulus.frac.den ≠
        0) :
    (encodeAnnulusBlocksFuel (Nat.succ (normNat annulus.frac.den)) annulus
      (Nat.lt_succ_self _)).continuation =
      let post := postInversion annulus residualNonzero
      let normalized := normalizeLoop post.frac
        (normNat annulus.frac.den) post.den_descent rfl
      let block : Block :=
        ⟨.regular, normalized.exponent,
          Sector.select normalized.annulus.frac.value⟩
      block :: (encodeAnnulusBlocksFuel (normNat annulus.frac.den)
        normalized.annulus normalized.measure_lt).continuation := by
  rw [encodeAnnulusBlocksFuel]
  simp only [dif_neg (Nat.lt_irrefl _), dif_neg residualNonzero]

private theorem encodeAnnulusBlocksFuel_continuation_eq :
    ∀ fuel annulus bound,
      (encodeAnnulusBlocksFuel fuel annulus bound).continuation =
        (encodeAnnulusBlocks annulus).continuation
  | 0, annulus, bound => False.elim (Nat.not_lt_zero _ bound)
  | fuel + 1, annulus, bound => by
      rw [encodeAnnulusBlocksFuel]
      split
      · rename_i slack
        exact encodeAnnulusBlocksFuel_continuation_eq fuel annulus slack
      · rename_i noSlack
        have measureEq : normNat annulus.frac.den = fuel :=
          Nat.le_antisymm (Nat.le_of_lt_succ bound)
            (Nat.le_of_not_gt noSlack)
        subst fuel
        unfold encodeAnnulusBlocks
        rw [encodeAnnulusBlocksFuel]
        simp only [dif_neg (Nat.lt_irrefl _)]

/-- Transparent computation equation for the completed-block list.  This
projection omits the proof-bearing reconstruction fields, allowing concrete
examples to reduce entirely in the kernel. -/
theorem encodeAnnulusBlocks_continuation_eq (annulus : Annulus) :
    (encodeAnnulusBlocks annulus).continuation =
      let sector := Sector.select annulus.frac.value
      let residual :=
        annulus.frac.num - sectorInt sector * annulus.frac.den
      if residualZero : residual = 0 then
        []
      else
        let post := postInversion annulus (by
          simpa only [residual, sector] using residualZero)
        let normalized := normalizeLoop post.frac
          (normNat annulus.frac.den) post.den_descent rfl
        let block : Block :=
          ⟨.regular, normalized.exponent,
            Sector.select normalized.annulus.frac.value⟩
        block :: (encodeAnnulusBlocks normalized.annulus).continuation := by
  by_cases residualZero :
      annulus.frac.num -
          sectorInt (Sector.select annulus.frac.value) * annulus.frac.den = 0
  · simp only [dif_pos residualZero]
    simpa only [encodeAnnulusBlocks] using
      encodeAnnulusBlocksFuel_continuation_of_eq annulus residualZero
  · simp only [dif_neg residualZero]
    let post := postInversion annulus residualZero
    let normalized := normalizeLoop post.frac
      (normNat annulus.frac.den) post.den_descent rfl
    let block : Block :=
      ⟨.regular, normalized.exponent,
        Sector.select normalized.annulus.frac.value⟩
    change (encodeAnnulusBlocks annulus).continuation =
      block :: (encodeAnnulusBlocks normalized.annulus).continuation
    calc
      (encodeAnnulusBlocks annulus).continuation =
          block :: (encodeAnnulusBlocksFuel (normNat annulus.frac.den)
            normalized.annulus normalized.measure_lt).continuation := by
        simpa only [encodeAnnulusBlocks, post, normalized, block] using
          encodeAnnulusBlocksFuel_continuation_of_ne annulus residualZero
      _ = block :: (encodeAnnulusBlocks normalized.annulus).continuation :=
        congrArg (List.cons block)
          (encodeAnnulusBlocksFuel_continuation_eq _ _ _)

/-- A nonterminal annulus emits one regular block and continues from the
normalized post-inversion annulus.  Naming the nonzero residual in the
statement keeps concrete evaluation independent of proof-term choices made
inside the dependent branch of `encodeAnnulusBlocks`. -/
theorem encodeAnnulusBlocks_continuation_of_ne (annulus : Annulus)
    (residualNonzero :
      annulus.frac.num -
          sectorInt (Sector.select annulus.frac.value) * annulus.frac.den ≠
        0) :
    (encodeAnnulusBlocks annulus).continuation =
      let post := postInversion annulus residualNonzero
      let normalized := normalizeLoop post.frac
        (normNat annulus.frac.den) post.den_descent rfl
      let block : Block :=
        ⟨.regular, normalized.exponent,
          Sector.select normalized.annulus.frac.value⟩
      block :: (encodeAnnulusBlocks normalized.annulus).continuation := by
  rw [encodeAnnulusBlocks_continuation_eq]
  simp only [dif_neg residualNonzero]

/-- A zero residual terminates the completed-block list. -/
theorem encodeAnnulusBlocks_continuation_of_eq (annulus : Annulus)
    (residualZero :
      annulus.frac.num -
          sectorInt (Sector.select annulus.frac.value) * annulus.frac.den =
        0) :
    (encodeAnnulusBlocks annulus).continuation = [] := by
  rw [encodeAnnulusBlocks_continuation_eq]
  simp only [dif_pos residualZero]

/-- The computationally observable part of one nonterminal annulus step.
Proof-bearing normalization data remain internal to the construction. -/
structure AnnulusStep where
  block : Block
  next : Annulus

/-- Exact Gaussian-integer residual tested by one annulus step. -/
def annulusResidual (annulus : Annulus) : GaussianInt :=
  annulus.frac.num -
    sectorInt (Sector.select annulus.frac.value) * annulus.frac.den

/-- Compute the emitted regular block and next normalized annulus. -/
def annulusStep (annulus : Annulus)
    (residualNonzero : annulusResidual annulus ≠ 0) : AnnulusStep :=
  let post := postInversion annulus (by
    simpa only [annulusResidual] using residualNonzero)
  let normalized := normalizeLoop post.frac
    (normNat annulus.frac.den) post.den_descent rfl
  ⟨⟨.regular, normalized.exponent,
      Sector.select normalized.annulus.frac.value⟩,
    normalized.annulus⟩

/-- Proof-erased one-step computation equation for the recursive block list. -/
theorem encodeAnnulusBlocks_continuation_of_ne_step (annulus : Annulus)
    (residualNonzero : annulusResidual annulus ≠ 0) :
    (encodeAnnulusBlocks annulus).continuation =
      (annulusStep annulus residualNonzero).block ::
        (encodeAnnulusBlocks
          (annulusStep annulus residualNonzero).next).continuation := by
  let directNonzero :
      annulus.frac.num -
          sectorInt (Sector.select annulus.frac.value) * annulus.frac.den ≠
        0 := by
    simpa only [annulusResidual] using residualNonzero
  simpa only [annulusStep] using
    encodeAnnulusBlocks_continuation_of_ne annulus directNonzero

/-- Proof-erased terminal equation stated through `annulusResidual`. -/
theorem encodeAnnulusBlocks_continuation_of_residual_eq (annulus : Annulus)
    (residualZero : annulusResidual annulus = 0) :
    (encodeAnnulusBlocks annulus).continuation = [] :=
  encodeAnnulusBlocks_continuation_of_eq annulus (by
    simpa only [annulusResidual] using residualZero)

/-- Complete finite block encoding of a nonzero uncancelled integral
fraction, retaining the exact projective realization point. -/
structure BlockEncoding (fraction : Frac) where
  blocks : List Block
  point : Proj
  realizes : ProjectiveRealizes blocks point
  reconstruct : point.Equivalent (CCL.Proj.affine fraction.value)

private def encodeHighBlocks (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0)
    (highBranch : 2 * normNat fraction.den ≤ normNat fraction.num) :
    BlockEncoding fraction := by
  let scan := CCL.Normalization.high
    (normNat fraction.num) (normNat fraction.den)
    (normNat_pos fraction.den_ne) highBranch
  let initial := initialHigh fraction numeratorNonzero highBranch
  let suffix := encodeAnnulusBlocks initial.annulus
  let block : Block :=
    ⟨.regular, scan.exponent,
      Sector.select initial.annulus.frac.value⟩
  let point := CCL.Mat2.act block.matrix suffix.tail.point
  have numeratorIdentity : initial.annulus.frac.num = fraction.num := by
    rfl
  have denominatorIdentity : initial.annulus.frac.den =
      natPow gammaInt scan.exponent * fraction.den := by
    rfl
  have scaledValue :
      RFAP.ConstructiveGaussian.Gaussian.natPow
          RFAP.ConstructiveGaussian.Gaussian.gamma scan.exponent *
        initial.annulus.frac.value = fraction.value :=
    value_of_scaled_den fraction initial.annulus.frac scan.exponent
      numeratorIdentity denominatorIdentity
  refine
    ⟨block :: suffix.continuation, point,
      ProjectiveRealizes.step block suffix.tail suffix.realizes, ?_⟩
  have acted : point.Equivalent
      (CCL.Mat2.act block.matrix suffix.tail.model.point) :=
    CCL.Mat2.act_respects_equivalent block.matrix suffix.tail.equivalent
  have modeled :
      (CCL.Mat2.act block.matrix suffix.tail.model.point).Equivalent
        (CCL.Proj.affine fraction.value) := by
    dsimp only [block, CCL.Cylinder.Block.matrix]
    exact CCL.Cylinder.Tail.regularBlock_act_equivalent
      scan.exponent suffix.tail.model initial.annulus.frac.value
      fraction.value suffix.models scaledValue
  exact CCL.Chordal.Proj.equivalent_trans acted modeled
    (block.act_model_valid suffix.tail)
    (CCL.Chordal.Proj.affine_hasNonzeroCoordinate fraction.value)

private def encodeLowBlocks (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0)
    (lowBranch : normNat fraction.num < 2 * normNat fraction.den) :
    BlockEncoding fraction := by
  let scan := CCL.Normalization.low
    (normNat fraction.num) (normNat fraction.den)
    (normNat_pos numeratorNonzero) (normNat_pos fraction.den_ne) lowBranch
  let initial := initialLow fraction numeratorNonzero lowBranch
  let suffix := encodeAnnulusBlocks initial.annulus
  let block : Block :=
    ⟨.initialLow, scan.exponent,
      Sector.select initial.annulus.frac.value⟩
  let point := CCL.Mat2.act block.matrix suffix.tail.point
  have numeratorIdentity : initial.annulus.frac.num =
      natPow gammaInt scan.exponent * fraction.num := by
    rfl
  have denominatorIdentity : initial.annulus.frac.den = fraction.den := by
    rfl
  have scaledValue : initial.annulus.frac.value =
      RFAP.ConstructiveGaussian.Gaussian.natPow
          RFAP.ConstructiveGaussian.Gaussian.gamma scan.exponent *
        fraction.value :=
    value_of_scaled_num fraction initial.annulus.frac scan.exponent
      numeratorIdentity denominatorIdentity
  refine
    ⟨block :: suffix.continuation, point,
      ProjectiveRealizes.step block suffix.tail suffix.realizes, ?_⟩
  have acted : point.Equivalent
      (CCL.Mat2.act block.matrix suffix.tail.model.point) :=
    CCL.Mat2.act_respects_equivalent block.matrix suffix.tail.equivalent
  have modeled :
      (CCL.Mat2.act block.matrix suffix.tail.model.point).Equivalent
        (CCL.Proj.affine fraction.value) := by
    dsimp only [block, CCL.Cylinder.Block.matrix]
    exact CCL.Cylinder.Tail.lowBlock_act_equivalent
      scan.exponent suffix.tail.model initial.annulus.frac.value
      fraction.value suffix.models scaledValue
  exact CCL.Chordal.Proj.equivalent_trans acted modeled
    (block.act_model_valid suffix.tail)
    (CCL.Chordal.Proj.affine_hasNonzeroCoordinate fraction.value)

/-- Algorithm 6.3 as a finite list of completed shrinking blocks. -/
def encodeBlocks (fraction : Frac) (numeratorNonzero : fraction.num ≠ 0) :
    BlockEncoding fraction :=
  if highBranch : 2 * normNat fraction.den ≤ normNat fraction.num then
    encodeHighBlocks fraction numeratorNonzero highBranch
  else
    encodeLowBlocks fraction numeratorNonzero (Nat.lt_of_not_ge highBranch)

/-- Transparent initial-branch equation for the completed block list.  It is
the finite evaluator interface used by exact manuscript examples. -/
theorem encodeBlocks_blocks_eq (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0) :
    (encodeBlocks fraction numeratorNonzero).blocks =
      if highBranch : 2 * normNat fraction.den ≤ normNat fraction.num then
        let scan := CCL.Normalization.high
          (normNat fraction.num) (normNat fraction.den)
          (normNat_pos fraction.den_ne) highBranch
        let initial := initialHigh fraction numeratorNonzero highBranch
        let block : Block :=
          ⟨.regular, scan.exponent,
            Sector.select initial.annulus.frac.value⟩
        block :: (encodeAnnulusBlocks initial.annulus).continuation
      else
        let lowBranch := Nat.lt_of_not_ge highBranch
        let scan := CCL.Normalization.low
          (normNat fraction.num) (normNat fraction.den)
          (normNat_pos numeratorNonzero) (normNat_pos fraction.den_ne)
          lowBranch
        let initial := initialLow fraction numeratorNonzero lowBranch
        let block : Block :=
          ⟨.initialLow, scan.exponent,
            Sector.select initial.annulus.frac.value⟩
        block :: (encodeAnnulusBlocks initial.annulus).continuation := by
  unfold encodeBlocks
  split <;> rfl

/-- Computation equation for the high initial normalization branch. -/
theorem encodeBlocks_blocks_of_high (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0)
    (highBranch : 2 * normNat fraction.den ≤ normNat fraction.num) :
    (encodeBlocks fraction numeratorNonzero).blocks =
      let scan := CCL.Normalization.high
        (normNat fraction.num) (normNat fraction.den)
        (normNat_pos fraction.den_ne) highBranch
      let initial := initialHigh fraction numeratorNonzero highBranch
      let block : Block :=
        ⟨.regular, scan.exponent,
          Sector.select initial.annulus.frac.value⟩
      block :: (encodeAnnulusBlocks initial.annulus).continuation := by
  rw [encodeBlocks_blocks_eq]
  simp only [dif_pos highBranch]

/-- Computation equation for the low initial normalization branch. -/
theorem encodeBlocks_blocks_of_low (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0)
    (lowBranch : normNat fraction.num < 2 * normNat fraction.den) :
    (encodeBlocks fraction numeratorNonzero).blocks =
      let scan := CCL.Normalization.low
        (normNat fraction.num) (normNat fraction.den)
        (normNat_pos numeratorNonzero) (normNat_pos fraction.den_ne)
        lowBranch
      let initial := initialLow fraction numeratorNonzero lowBranch
      let block : Block :=
        ⟨.initialLow, scan.exponent,
          Sector.select initial.annulus.frac.value⟩
      block :: (encodeAnnulusBlocks initial.annulus).continuation := by
  rw [encodeBlocks_blocks_eq]
  simp only [dif_neg (Nat.not_le_of_lt lowBranch)]

/-- The computationally observable initial block and loop annulus. -/
structure InitialBlockStep where
  block : Block
  annulus : Annulus

/-- Compute the high-branch initial block and loop annulus. -/
def initialHighBlockStep (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0)
    (highBranch : 2 * normNat fraction.den ≤ normNat fraction.num) :
    InitialBlockStep :=
  let scan := CCL.Normalization.high
    (normNat fraction.num) (normNat fraction.den)
    (normNat_pos fraction.den_ne) highBranch
  let initial := initialHigh fraction numeratorNonzero highBranch
  ⟨⟨.regular, scan.exponent,
      Sector.select initial.annulus.frac.value⟩,
    initial.annulus⟩

/-- Compute the low-branch initial block and loop annulus. -/
def initialLowBlockStep (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0)
    (lowBranch : normNat fraction.num < 2 * normNat fraction.den) :
    InitialBlockStep :=
  let scan := CCL.Normalization.low
    (normNat fraction.num) (normNat fraction.den)
    (normNat_pos numeratorNonzero) (normNat_pos fraction.den_ne) lowBranch
  let initial := initialLow fraction numeratorNonzero lowBranch
  ⟨⟨.initialLow, scan.exponent,
      Sector.select initial.annulus.frac.value⟩,
    initial.annulus⟩

/-- A certified pair of adjacent power bounds determines the observable
high-branch exponent without replaying the bounded search. -/
theorem initialHighBlockStep_exponent_eq_of_bounds (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0)
    (highBranch : 2 * normNat fraction.den ≤ normNat fraction.num)
    (candidate : Nat)
    (candidateLower :
      2 ^ candidate * normNat fraction.den ≤ normNat fraction.num)
    (candidateUpper :
      normNat fraction.num <
        2 ^ (candidate + 1) * normNat fraction.den) :
    (initialHighBlockStep fraction numeratorNonzero highBranch).block.exponent =
      candidate := by
  unfold initialHighBlockStep
  dsimp only
  exact (CCL.Normalization.high
    (normNat fraction.num) (normNat fraction.den)
    (normNat_pos fraction.den_ne) highBranch).exponent_eq_of_bounds
      candidateLower candidateUpper

/-- The high initial state retains the original numerator. -/
theorem initialHighBlockStep_num_eq (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0)
    (highBranch : 2 * normNat fraction.den ≤ normNat fraction.num) :
    (initialHighBlockStep fraction numeratorNonzero highBranch).annulus.frac.num =
      fraction.num := by
  rfl

/-- The high initial denominator is scaled by the observable exponent. -/
theorem initialHighBlockStep_den_eq (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0)
    (highBranch : 2 * normNat fraction.den ≤ normNat fraction.num) :
    (initialHighBlockStep fraction numeratorNonzero highBranch).annulus.frac.den =
      natPow gammaInt
          (initialHighBlockStep fraction numeratorNonzero highBranch).block.exponent *
        fraction.den := by
  rfl

/-- Observable high initial blocks use the sector of their returned annulus. -/
theorem initialHighBlockStep_block_eq (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0)
    (highBranch : 2 * normNat fraction.den ≤ normNat fraction.num) :
    (initialHighBlockStep fraction numeratorNonzero highBranch).block =
      ⟨.regular,
        (initialHighBlockStep fraction numeratorNonzero highBranch).block.exponent,
        Sector.select
          (initialHighBlockStep fraction numeratorNonzero highBranch).annulus.frac.value⟩ := by
  rfl

/-- The next annulus numerator is the preceding denominator. -/
theorem annulusStep_next_num_eq (annulus : Annulus)
    (residualNonzero : annulusResidual annulus ≠ 0) :
    (annulusStep annulus residualNonzero).next.frac.num =
      annulus.frac.den := by
  rfl

/-- The next annulus denominator is the scaled inverted residual. -/
theorem annulusStep_next_den_eq (annulus : Annulus)
    (residualNonzero : annulusResidual annulus ≠ 0) :
    (annulusStep annulus residualNonzero).next.frac.den =
      natPow gammaInt (annulusStep annulus residualNonzero).block.exponent *
        (gammaInt * annulusResidual annulus) := by
  rfl

/-- Observable nonterminal blocks use the sector of the returned annulus. -/
theorem annulusStep_block_eq (annulus : Annulus)
    (residualNonzero : annulusResidual annulus ≠ 0) :
    (annulusStep annulus residualNonzero).block =
      ⟨.regular,
        (annulusStep annulus residualNonzero).block.exponent,
        Sector.select (annulusStep annulus residualNonzero).next.frac.value⟩ := by
  rfl

/-- Adjacent loop power bounds determine the observable exponent of a
nonterminal annulus step without reducing the search fuel. -/
theorem annulusStep_exponent_eq_of_bounds (annulus : Annulus)
    (residualNonzero : annulusResidual annulus ≠ 0)
    (candidate : Nat)
    (candidateLower :
      2 ^ candidate * normNat (gammaInt * annulusResidual annulus) <
        normNat annulus.frac.den)
    (candidateUpper :
      normNat annulus.frac.den ≤
        2 ^ (candidate + 1) *
          normNat (gammaInt * annulusResidual annulus)) :
    (annulusStep annulus residualNonzero).block.exponent = candidate := by
  let directNonzero :
      annulus.frac.num -
          sectorInt (Sector.select annulus.frac.value) * annulus.frac.den ≠
        0 := by
    simpa only [annulusResidual] using residualNonzero
  let post := postInversion annulus directNonzero
  let normalized := normalizeLoop post.frac
    (normNat annulus.frac.den) post.den_descent rfl
  change normalized.exponent = candidate
  dsimp only [normalized, normalizeLoop]
  apply (CCL.Normalization.loop
    (normNat post.frac.num) (normNat post.frac.den)
    (normNat_pos post.frac.den_ne) post.den_descent).exponent_eq_of_bounds
  · rw [post.num_eq, post.den_eq]
    simpa only [annulusResidual] using candidateLower
  · rw [post.num_eq, post.den_eq]
    simpa only [annulusResidual] using candidateUpper

/-- Proof-erased high-branch equation for exact evaluation. -/
theorem encodeBlocks_blocks_of_high_step (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0)
    (highBranch : 2 * normNat fraction.den ≤ normNat fraction.num) :
    (encodeBlocks fraction numeratorNonzero).blocks =
      (initialHighBlockStep fraction numeratorNonzero highBranch).block ::
        (encodeAnnulusBlocks
          (initialHighBlockStep fraction numeratorNonzero highBranch).annulus).continuation := by
  simpa only [initialHighBlockStep] using
    encodeBlocks_blocks_of_high fraction numeratorNonzero highBranch

/-- Proof-erased low-branch equation for exact evaluation. -/
theorem encodeBlocks_blocks_of_low_step (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0)
    (lowBranch : normNat fraction.num < 2 * normNat fraction.den) :
    (encodeBlocks fraction numeratorNonzero).blocks =
      (initialLowBlockStep fraction numeratorNonzero lowBranch).block ::
        (encodeAnnulusBlocks
          (initialLowBlockStep fraction numeratorNonzero lowBranch).annulus).continuation := by
  simpa only [initialLowBlockStep] using
    encodeBlocks_blocks_of_low fraction numeratorNonzero lowBranch

/-- The encoded homogeneous point carries a valid finite cylinder realization. -/
def encodeBlocks_realizes (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0) :
    ProjectiveRealizes
      (encodeBlocks fraction numeratorNonzero).blocks
      (encodeBlocks fraction numeratorNonzero).point :=
  (encodeBlocks fraction numeratorNonzero).realizes

/-- The completed-block realization reconstructs the exact input value up to
the finite projective equivalence relation. -/
theorem encodeBlocks_reconstruct (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0) :
    (encodeBlocks fraction numeratorNonzero).point.Equivalent
      (CCL.Proj.affine fraction.value) :=
  (encodeBlocks fraction numeratorNonzero).reconstruct

/-- A suffix beginning with a sector code and its exact integral decoder. -/
structure TailEncoding (annulus : Annulus) where
  word : Word
  matrix : IntegralMat2
  reconstruct :
    CCL.Proj.Equivalent
      (CCL.Mat2.act matrix (CCL.Proj.omega : IntegralProj))
      ⟨annulus.frac.num, annulus.frac.den⟩

private theorem terminal_reconstruct (annulus : Annulus) (sector : Sector)
    (residualZero :
      annulus.frac.num - sectorInt sector * annulus.frac.den = 0) :
    CCL.Proj.Equivalent
      (CCL.Mat2.act (sectorMatrixInt sector)
        (CCL.Proj.omega : IntegralProj))
      ⟨annulus.frac.num, annulus.frac.den⟩ := by
  have numeratorIdentity :
      annulus.frac.num = sectorInt sector * annulus.frac.den :=
    sub_eq_zero.mp residualZero
  rw [numeratorIdentity]
  dsimp only [CCL.Proj.Equivalent, sectorMatrixInt, CCL.Mat2.act,
    CCL.Mat2.mul, CCL.Mat2.translate, CCL.Mat2.invert, CCL.Proj.omega]
  ring1

private theorem normalized_step_reconstruct (annulus : Annulus)
    (post : PostInversion annulus)
    (normalized : LoopResult post.frac (normNat annulus.frac.den)) :
    CCL.Proj.Equivalent
      (CCL.Mat2.act
        (CCL.Mat2.mul
          (sectorMatrixInt (Sector.select annulus.frac.value))
          (CCL.Mat2.scale (natPow gammaInt normalized.exponent)))
        ⟨normalized.annulus.frac.num, normalized.annulus.frac.den⟩)
      ⟨annulus.frac.num, annulus.frac.den⟩ := by
  rw [normalized.num_eq, normalized.den_eq, post.num_eq, post.den_eq]
  dsimp only [CCL.Proj.Equivalent, sectorMatrixInt, CCL.Mat2.act,
    CCL.Mat2.mul, CCL.Mat2.translate, CCL.Mat2.invert, CCL.Mat2.scale]
  rw [GaussianInt.sub_eq_add_neg]
  ring1

private theorem normalized_step_den_ne (annulus : Annulus)
    (post : PostInversion annulus)
    (normalized : LoopResult post.frac (normNat annulus.frac.den)) :
    (CCL.Mat2.act
      (CCL.Mat2.mul
        (sectorMatrixInt (Sector.select annulus.frac.value))
        (CCL.Mat2.scale (natPow gammaInt normalized.exponent)))
      ⟨normalized.annulus.frac.num, normalized.annulus.frac.den⟩).q ≠ 0 := by
  rw [normalized.num_eq, normalized.den_eq, post.num_eq]
  dsimp only [sectorMatrixInt, CCL.Mat2.act, CCL.Mat2.mul,
    CCL.Mat2.translate, CCL.Mat2.invert, CCL.Mat2.scale]
  simpa only [zero_add, one_mul, mul_zero, add_zero, zero_mul] using
    GaussianInt.mul_ne_zero
      (GaussianInt.mul_ne_zero (show gammaInt ≠ 0 by decide)
        (natPow_ne_zero gammaInt (by decide) normalized.exponent))
      annulus.frac.den_ne

/-- Integral reconstruction core for the annulus macro-recursion.  The public
encoder attaches the emitted word from the structurally recursive block
trace below. -/
private def encodeTailCore (annulus : Annulus) : TailEncoding annulus :=
  let sector := Sector.select annulus.frac.value
  let residual :=
    annulus.frac.num - sectorInt sector * annulus.frac.den
  if residualZero : residual = 0 then
    ⟨sector.code, sectorMatrixInt sector,
      terminal_reconstruct annulus sector (by
        simpa only [residual, sector] using residualZero)⟩
  else
    let post := postInversion annulus (by
      simpa only [residual, sector] using residualZero)
    let normalized := normalizeLoop post.frac (normNat annulus.frac.den)
      post.den_descent rfl
    let tail := encodeTailCore normalized.annulus
    let factor := CCL.Mat2.mul (sectorMatrixInt sector)
      (CCL.Mat2.scale (natPow gammaInt normalized.exponent))
    let matrix := CCL.Mat2.mul factor tail.matrix
    ⟨sector.code ++ List.replicate normalized.exponent true ++
        [false] ++ tail.word,
      matrix, by
        dsimp only [matrix]
        rw [CCL.Mat2.act_mul]
        have acted := CCL.Mat2.act_respects_equivalent factor tail.reconstruct
        exact GaussianInt.equivalent_trans_of_mid_q acted
          (normalized_step_reconstruct annulus post normalized)
          (normalized_step_den_ne annulus post normalized)⟩
termination_by normNat annulus.frac.den
decreasing_by exact normalized.measure_lt

/-- Integral decoder data with its raw word taken directly from the certified
completed-block trace. -/
def encodeTail (annulus : Annulus) : TailEncoding annulus :=
  let core := encodeTailCore annulus
  { word := (Sector.select annulus.frac.value).code ++
      rawWord (encodeAnnulusBlocks annulus).continuation
    matrix := core.matrix
    reconstruct := core.reconstruct }

/-- The integral decoder word and the completed-block trace are two views of
the same finite run.  The former retains the current sector header; the latter
stores precisely the completed blocks that follow it. -/
theorem encodeTail_word_eq (annulus : Annulus) :
    (encodeTail annulus).word =
      (Sector.select annulus.frac.value).code ++
        rawWord (encodeAnnulusBlocks annulus).continuation := rfl

/-- Complete encoding, including its exact integral decoder product. -/
structure Encoding (fraction : Frac) where
  word : Word
  matrix : IntegralMat2
  reconstruct :
    CCL.Proj.Equivalent
      (CCL.Mat2.act matrix (CCL.Proj.omega : IntegralProj))
      ⟨fraction.num, fraction.den⟩

private def finishInitial {fraction : Frac}
    (initial : InitialResult fraction) : Encoding fraction :=
  let tail := encodeTail initial.annulus
  let matrix := CCL.Mat2.mul initial.radial tail.matrix
  ⟨initial.header ++ tail.word, matrix, by
    dsimp only [matrix]
    rw [CCL.Mat2.act_mul]
    have acted := CCL.Mat2.act_respects_equivalent
      initial.radial tail.reconstruct
    exact GaussianInt.equivalent_trans_of_mid_q acted
      initial.radial_reconstruct initial.radial_den_ne⟩

/-- Algorithm 6.3 with exact finite reconstruction evidence. -/
def encodeResult (fraction : Frac) (numeratorNonzero : fraction.num ≠ 0) :
    Encoding fraction :=
  if highBranch : 2 * normNat fraction.den ≤ normNat fraction.num then
    finishInitial (initialHigh fraction numeratorNonzero highBranch)
  else
    finishInitial (initialLow fraction numeratorNonzero
      (Nat.lt_of_not_ge highBranch))

/-- Raw binary word emitted by the constructive encoder. -/
def encode (fraction : Frac) (numeratorNonzero : fraction.num ≠ 0) : Word :=
  (encodeResult fraction numeratorNonzero).word

/-- Integral reconstruction statement for the emitted decoder. -/
theorem encode_reconstruct_pair (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0) :
    CCL.Proj.Equivalent
      (CCL.Mat2.act (encodeResult fraction numeratorNonzero).matrix
        (CCL.Proj.omega : IntegralProj))
      ⟨fraction.num, fraction.den⟩ :=
  (encodeResult fraction numeratorNonzero).reconstruct

/-- Constructive Gaussian/projective reconstruction of the encoded value. -/
theorem encode_reconstruct (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0) :
    CCL.Proj.Equivalent
      (CCL.Mat2.act (mapMat (encodeResult fraction numeratorNonzero).matrix)
        (CCL.Proj.omega : Proj))
      (CCL.Proj.affine fraction.value) := by
  have mapped := mapProj_equivalent
    (encodeResult fraction numeratorNonzero).reconstruct
  rw [mapProj_act, mapProj_omega] at mapped
  dsimp only [CCL.Proj.Equivalent, mapProj, CCL.Proj.affine] at mapped ⊢
  rw [RFAP.ConstructiveGaussian.Gaussian.mul_one]
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    fraction.den_toGaussian_ne
  calc
    (CCL.Mat2.act (mapMat (encodeResult fraction numeratorNonzero).matrix)
        (CCL.Proj.omega : Proj)).p * toGaussian fraction.den =
        toGaussian fraction.num *
          (CCL.Mat2.act
            (mapMat (encodeResult fraction numeratorNonzero).matrix)
            (CCL.Proj.omega : Proj)).q := mapped
    _ = (fraction.value * toGaussian fraction.den) *
        (CCL.Mat2.act
          (mapMat (encodeResult fraction numeratorNonzero).matrix)
          (CCL.Proj.omega : Proj)).q := by rw [fraction.value_mul_den]
    _ = (fraction.value *
        (CCL.Mat2.act
          (mapMat (encodeResult fraction numeratorNonzero).matrix)
          (CCL.Proj.omega : Proj)).q) * toGaussian fraction.den := by
      ring1

/-- The raw integral word and the completed-block list are extensionally the
same encoder output. -/
theorem encode_eq_rawWord (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0) :
    encode fraction numeratorNonzero =
      rawWord (encodeBlocks fraction numeratorNonzero).blocks := by
  rw [encode, encodeResult, encodeBlocks]
  split
  · rename_i highBranch
    dsimp only [finishInitial, encodeHighBlocks]
    rw [encodeTail_word_eq]
    simp only [initialHigh, rawWord_cons, Block.word,
      CCL.Decoder.regularWord, List.append_assoc,
      List.cons_append, List.nil_append]
  · rename_i highBranch
    dsimp only [finishInitial, encodeLowBlocks]
    rw [encodeTail_word_eq]
    simp only [initialLow, rawWord_cons, Block.word,
      CCL.Decoder.lowWord,
      CCL.Decoder.regularWord, List.append_assoc,
      List.cons_append, List.nil_append]

/-- Two explicit nonzero fractions emitted into the same completed-block
cylinder satisfy its constructive squared-chordal width bound. -/
theorem chordalSq_le_of_encodeBlocks_eq (left right : Frac)
    (leftNumeratorNonzero : left.num ≠ 0)
    (rightNumeratorNonzero : right.num ≠ 0)
    (blocksEqual :
      (encodeBlocks left leftNumeratorNonzero).blocks =
        (encodeBlocks right rightNumeratorNonzero).blocks) :
    CCL.Chordal.chordalSq
        (CCL.Proj.affine left.value) (CCL.Proj.affine right.value) ≤
      (1 / 2 : Coordinate) ^
        (encodeBlocks left leftNumeratorNonzero).blocks.length := by
  let leftEncoding := encodeBlocks left leftNumeratorNonzero
  let rightEncoding := encodeBlocks right rightNumeratorNonzero
  have rightRealizes : ProjectiveRealizes leftEncoding.blocks
      rightEncoding.point := by
    rw [blocksEqual]
    exact rightEncoding.realizes
  have encodedBound :
      CCL.Chordal.chordalSq
          leftEncoding.point rightEncoding.point ≤
        (1 / 2 : Coordinate) ^ leftEncoding.blocks.length :=
    ProjectiveRealizes.chordalSq_le_half_pow
      leftEncoding.realizes rightRealizes
  calc
    CCL.Chordal.chordalSq
        (CCL.Proj.affine left.value) (CCL.Proj.affine right.value) =
        CCL.Chordal.chordalSq
          leftEncoding.point (CCL.Proj.affine right.value) :=
      (CCL.Chordal.chordalSq_eq_of_equivalent_left
        leftEncoding.realizes.valid
        (CCL.Chordal.Proj.affine_hasNonzeroCoordinate left.value)
        leftEncoding.reconstruct (CCL.Proj.affine right.value)).symm
    _ = CCL.Chordal.chordalSq
        leftEncoding.point rightEncoding.point :=
      (CCL.Chordal.chordalSq_eq_of_equivalent_right
        rightEncoding.realizes.valid
        (CCL.Chordal.Proj.affine_hasNonzeroCoordinate right.value)
        rightEncoding.reconstruct leftEncoding.point).symm
    _ ≤ (1 / 2 : Coordinate) ^ leftEncoding.blocks.length := encodedBound

end CCL.Encoder
