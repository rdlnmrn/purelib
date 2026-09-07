import CCL.Encoding.Decoder
import CCL.Integral

/-!
# Executable complex continued-logarithm encoder

This is Algorithm 6.3 as a total Lean function on uncancelled Gaussian-integer
fractions.  Initial and loop normalization use the bounded scans from Lemma
3.1.  The recursive annulus call is accepted only after proving the exact
strict denominator-norm decrease from Theorem 6.5.
-/

namespace CCL

open GaussianRat
open Integral

namespace CCLEncoder

private theorem gammaPow_ne (k : ℕ) : gammaInt ^ k ≠ 0 := by
  exact pow_ne_zero _ (by decide)

/-- Integral version of the low-header matrix `E⁻ₘ`. -/
def lowScaleInt (m : ℕ) : Mat2 GI := ⟨1, 0, 0, gammaInt ^ m⟩

/-- The sector subtraction/inversion matrix `Tₛ Iγ`. -/
def sectorMatrixInt (s : Sector) : Mat2 GI :=
  Mat2.mul (Mat2.translate (sectorInt s)) (Mat2.invert gammaInt)

/-- Integral form of the completed regular block (6.2). -/
def regularBlockInt (k : ℕ) (s : Sector) : Mat2 GI :=
  Mat2.mul (Mat2.scale (gammaInt ^ k)) (sectorMatrixInt s)

/-- Integral form of the completed low initial block (6.3). -/
def lowBlockInt (m : ℕ) (s : Sector) : Mat2 GI :=
  Mat2.mul (lowScaleInt m) (sectorMatrixInt s)

/-- The integral regular block embeds to the decoder matrix (6.2). -/
theorem map_regularBlockInt (k : ℕ) (s : Sector) :
    mapMat (regularBlockInt k s) = CCLDecoder.regularBlock k s := by
  apply Mat2.ext <;> apply GaussianRat.ext <;>
    simp [mapMat, regularBlockInt, sectorMatrixInt, CCLDecoder.regularBlock,
      Mat2.mul, Mat2.scale, Mat2.translate, Mat2.invert] <;>
    ring

/-- The integral low block embeds to the decoder matrix (6.3). -/
theorem map_lowBlockInt (m : ℕ) (s : Sector) :
    mapMat (lowBlockInt m s) = CCLDecoder.lowBlock m s := by
  apply Mat2.ext <;> apply GaussianRat.ext <;>
    simp [mapMat, lowBlockInt, lowScaleInt, sectorMatrixInt, CCLDecoder.lowBlock,
      Mat2.mul, Mat2.translate, Mat2.invert] <;>
    ring

/-- A fraction certified to lie in the closed CCL band. -/
structure Annulus where
  frac : Frac
  band : Sector.Band frac.value

private theorem frac_entry_of_bounds (f : Frac)
    (hlower : normNat f.den ≤ normNat f.num)
    (hupper : normNat f.num < 2 * normNat f.den) : Sector.Entry f.value := by
  rw [Sector.Entry, Frac.normSq_value]
  have hd : (0 : ℚ) < normNat f.den := by exact_mod_cast normNat_pos f.den_ne
  constructor
  · apply (le_div_iff₀ hd).2
    norm_num
    exact_mod_cast hlower
  · apply (div_lt_iff₀ hd).2
    exact_mod_cast hupper

private theorem frac_loop_of_bounds (f : Frac)
    (hlower : normNat f.den < normNat f.num)
    (hupper : normNat f.num ≤ 2 * normNat f.den) : Sector.Loop f.value := by
  rw [Sector.Loop, Frac.normSq_value]
  have hd : (0 : ℚ) < normNat f.den := by exact_mod_cast normNat_pos f.den_ne
  constructor
  · apply (lt_div_iff₀ hd).2
    norm_num
    exact_mod_cast hlower
  · apply (div_le_iff₀ hd).2
    exact_mod_cast hupper

private theorem entry_band {z : GaussianRat} (h : Sector.Entry z) : Sector.Band z :=
  ⟨h.1, h.2.le⟩

private theorem loop_band {z : GaussianRat} (h : Sector.Loop z) : Sector.Band z :=
  ⟨h.1.le, h.2⟩

/-- Initial normalization, including the raw header, radial decoder factor,
and its reconstruction certificate. -/
structure InitialResult (f : Frac) where
  header : Prefix.Word
  radial : Mat2 GI
  annulus : Annulus
  radial_reconstruct :
    (Mat2.act radial ⟨annulus.frac.num, annulus.frac.den⟩).Equivalent
      ⟨f.num, f.den⟩
  radial_den_ne :
    (Mat2.act radial ⟨annulus.frac.num, annulus.frac.den⟩).q ≠ 0

/-- The high initial branch `1ᵏ0`. -/
def initialHigh (f : Frac) (_hnum : f.num ≠ 0)
    (hhigh : 2 * normNat f.den ≤ normNat f.num) : InitialResult f := by
  let scan := BinaryNormalization.high (normNat f.num) (normNat f.den)
    (normNat_pos f.den_ne) hhigh
  let den' := gammaInt ^ scan.exponent * f.den
  have hden' : den' ≠ 0 := mul_ne_zero (gammaPow_ne scan.exponent) f.den_ne
  let normalized : Frac := ⟨f.num, den', hden'⟩
  have hdenNorm : normNat den' = 2 ^ scan.exponent * normNat f.den := by
    simp [den', normNat_mul]
  have hlower : normNat normalized.den ≤ normNat normalized.num := by
    dsimp [normalized]
    rw [hdenNorm]
    exact scan.lower
  have hupper : normNat normalized.num < 2 * normNat normalized.den := by
    dsimp [normalized]
    rw [hdenNorm]
    calc
      normNat f.num < 2 ^ (scan.exponent + 1) * normNat f.den := scan.upper
      _ = 2 * (2 ^ scan.exponent * normNat f.den) := by
        rw [pow_succ]
        ac_rfl
  have hentry := frac_entry_of_bounds normalized hlower hupper
  refine ⟨List.replicate scan.exponent true ++ [false],
    Mat2.scale (gammaInt ^ scan.exponent),
    ⟨normalized, entry_band hentry⟩, ?_, ?_⟩
  · dsimp [normalized, den', Proj.Equivalent, Mat2.act, Mat2.scale]
    ring
  · dsimp [normalized, Mat2.act, Mat2.scale]
    simpa using hden'

/-- The low initial branch `01ᵐ0`. -/
def initialLow (f : Frac) (hnum : f.num ≠ 0)
    (hlow : normNat f.num < 2 * normNat f.den) : InitialResult f := by
  let scan := BinaryNormalization.low (normNat f.num) (normNat f.den)
    (normNat_pos hnum) (normNat_pos f.den_ne) hlow
  let num' := gammaInt ^ scan.exponent * f.num
  let normalized : Frac := ⟨num', f.den, f.den_ne⟩
  have hnumNorm : normNat num' = 2 ^ scan.exponent * normNat f.num := by
    simp [num', normNat_mul]
  have hlower : normNat normalized.den ≤ normNat normalized.num := by
    dsimp [normalized]
    rw [hnumNorm]
    exact scan.lower
  have hupper : normNat normalized.num < 2 * normNat normalized.den := by
    dsimp [normalized]
    rw [hnumNorm]
    exact scan.upper
  have hentry := frac_entry_of_bounds normalized hlower hupper
  refine ⟨false :: List.replicate scan.exponent true ++ [false],
    lowScaleInt scan.exponent, ⟨normalized, entry_band hentry⟩, ?_, ?_⟩
  · dsimp [normalized, num', lowScaleInt, Proj.Equivalent, Mat2.act]
    ring
  · dsimp [normalized, lowScaleInt, Mat2.act]
    simpa using mul_ne_zero (gammaPow_ne scan.exponent) f.den_ne

/-- Data after a nonterminal sector subtraction and inversion. -/
structure PostInversion (old : Annulus) where
  frac : Frac
  num_eq : frac.num = old.frac.den
  den_eq : frac.den = gammaInt *
    (old.frac.num - sectorInt (Sector.select old.frac.value) * old.frac.den)
  den_descent : normNat frac.den < normNat old.frac.den

/-- One nonterminal sector step, with Lemma 6.4 converted to the natural measure. -/
def postInversion (old : Annulus)
    (hr : old.frac.num - sectorInt (Sector.select old.frac.value) * old.frac.den ≠ 0) :
    PostInversion old := by
  let s := Sector.select old.frac.value
  let r := old.frac.num - sectorInt s * old.frac.den
  have hr' : r ≠ 0 := by simpa [r, s] using hr
  let den' := gammaInt * r
  have hden' : den' ≠ 0 := mul_ne_zero (by decide) hr'
  let next : Frac := ⟨old.frac.den, den', hden'⟩
  have hdescRat := CCLDecoder.inversion_stage_descent
    (y := old.frac.value) (P := toRat old.frac.num) (Q := toRat old.frac.den)
    old.frac.den_toRat_ne old.band s (Sector.select_spec _ old.band.1)
    old.frac.value_mul_den.symm
  have hdenRat : toRat den' = gamma *
      (toRat old.frac.num - s.rep * toRat old.frac.den) := by
    simp [den', r]
  rw [← hdenRat, normSq_toRat, normSq_toRat] at hdescRat
  exact ⟨next, rfl, rfl, by exact_mod_cast hdescRat⟩

/-- Loop normalization result and the strict recursive-call measure. -/
structure LoopResult (post : Frac) (oldMeasure : ℕ) where
  exponent : ℕ
  annulus : Annulus
  num_eq : annulus.frac.num = post.num
  den_eq : annulus.frac.den = gammaInt ^ exponent * post.den
  measure_lt : normNat annulus.frac.den < oldMeasure

/-- Normalize a post-inversion state into `(1,2]` using Lemma 3.1(c). -/
def normalizeLoop (post : Frac) (oldMeasure : ℕ)
    (hpost : normNat post.den < normNat post.num)
    (hnumOld : normNat post.num = oldMeasure) : LoopResult post oldMeasure := by
  let scan := BinaryNormalization.loop (normNat post.num) (normNat post.den)
    (normNat_pos post.den_ne) hpost
  let den' := gammaInt ^ scan.exponent * post.den
  have hden' : den' ≠ 0 := mul_ne_zero (gammaPow_ne scan.exponent) post.den_ne
  let normalized : Frac := ⟨post.num, den', hden'⟩
  have hdenNorm : normNat den' = 2 ^ scan.exponent * normNat post.den := by
    simp [den', normNat_mul]
  have hlower : normNat normalized.den < normNat normalized.num := by
    dsimp [normalized]
    rw [hdenNorm]
    exact scan.lower
  have hupper : normNat normalized.num ≤ 2 * normNat normalized.den := by
    dsimp [normalized]
    rw [hdenNorm]
    calc
      normNat post.num ≤ 2 ^ (scan.exponent + 1) * normNat post.den := scan.upper
      _ = 2 * (2 ^ scan.exponent * normNat post.den) := by
        rw [pow_succ]
        ac_rfl
  have hloop := frac_loop_of_bounds normalized hlower hupper
  refine ⟨scan.exponent, ⟨normalized, loop_band hloop⟩, rfl, rfl, ?_⟩
  calc
    normNat normalized.den < normNat normalized.num := hlower
    _ = normNat post.num := rfl
    _ = oldMeasure := hnumOld

/-- A suffix beginning at a sector code, together with its exact integral
decoder product. -/
structure TailEncoding (a : Annulus) where
  word : Prefix.Word
  matrix : Mat2 GI
  reconstruct :
    (Mat2.act matrix (Proj.omega : Proj GI)).Equivalent
      ⟨a.frac.num, a.frac.den⟩

private theorem terminal_reconstruct (a : Annulus) (s : Sector)
    (hr : a.frac.num - sectorInt s * a.frac.den = 0) :
    (Mat2.act (sectorMatrixInt s) (Proj.omega : Proj GI)).Equivalent
      ⟨a.frac.num, a.frac.den⟩ := by
  have hnum : a.frac.num = sectorInt s * a.frac.den := sub_eq_zero.mp hr
  rw [hnum]
  dsimp [Proj.Equivalent, sectorMatrixInt, Mat2.act, Mat2.mul,
    Mat2.translate, Mat2.invert, Proj.omega]
  ring

private theorem normalized_step_reconstruct (a : Annulus)
    (post : PostInversion a)
    (normalized : LoopResult post.frac (normNat a.frac.den)) :
    (Mat2.act
      (Mat2.mul (sectorMatrixInt (Sector.select a.frac.value))
        (Mat2.scale (gammaInt ^ normalized.exponent)))
      ⟨normalized.annulus.frac.num, normalized.annulus.frac.den⟩).Equivalent
      ⟨a.frac.num, a.frac.den⟩ := by
  rw [normalized.num_eq, normalized.den_eq, post.num_eq, post.den_eq]
  dsimp [Proj.Equivalent, sectorMatrixInt, Mat2.act, Mat2.mul,
    Mat2.translate, Mat2.invert, Mat2.scale]
  ring

private theorem normalized_step_den_ne (a : Annulus)
    (post : PostInversion a)
    (normalized : LoopResult post.frac (normNat a.frac.den)) :
    (Mat2.act
      (Mat2.mul (sectorMatrixInt (Sector.select a.frac.value))
        (Mat2.scale (gammaInt ^ normalized.exponent)))
      ⟨normalized.annulus.frac.num, normalized.annulus.frac.den⟩).q ≠ 0 := by
  rw [normalized.num_eq, normalized.den_eq, post.num_eq]
  dsimp [sectorMatrixInt, Mat2.act, Mat2.mul, Mat2.translate, Mat2.invert,
    Mat2.scale]
  simpa using mul_ne_zero
    (mul_ne_zero (show gammaInt ≠ 0 by decide) (gammaPow_ne normalized.exponent))
    a.frac.den_ne

/-- The well-founded annulus macro-recursion from Theorem 6.5.  Alongside the
raw suffix it composes the decoder factors in emission order and proves that
their action on `ω` reconstructs the current annulus fraction. -/
def encodeTail (a : Annulus) : TailEncoding a :=
  let s := Sector.select a.frac.value
  let r := a.frac.num - sectorInt s * a.frac.den
  if hr : r = 0 then
    ⟨s.code, sectorMatrixInt s,
      terminal_reconstruct a s (by simpa [r, s] using hr)⟩
  else
    let post := postInversion a (by simpa [r, s] using hr)
    let normalized := normalizeLoop post.frac (normNat a.frac.den)
      post.den_descent rfl
    let tail := encodeTail normalized.annulus
    let factor := Mat2.mul (sectorMatrixInt s)
      (Mat2.scale (gammaInt ^ normalized.exponent))
    let matrix := Mat2.mul factor tail.matrix
    ⟨s.code ++ List.replicate normalized.exponent true ++ [false] ++ tail.word,
      matrix, by
        dsimp only [matrix]
        rw [Mat2.act_mul]
        have hact := Mat2.act_respects_equivalent factor tail.reconstruct
        exact hact.trans_of_mid_q_domain
          (normalized_step_reconstruct a post normalized)
          (normalized_step_den_ne a post normalized)⟩
termination_by normNat a.frac.den
decreasing_by exact normalized.measure_lt

/-- Prepending an initial radial factor to a certified annulus suffix. -/
structure Encoding (f : Frac) where
  word : Prefix.Word
  matrix : Mat2 GI
  reconstruct :
    (Mat2.act matrix (Proj.omega : Proj GI)).Equivalent ⟨f.num, f.den⟩

private def finishInitial {f : Frac} (initial : InitialResult f) : Encoding f :=
  let tail := encodeTail initial.annulus
  let matrix := Mat2.mul initial.radial tail.matrix
  ⟨initial.header ++ tail.word, matrix, by
    dsimp only [matrix]
    rw [Mat2.act_mul]
    have hact := Mat2.act_respects_equivalent initial.radial tail.reconstruct
    exact hact.trans_of_mid_q_domain initial.radial_reconstruct initial.radial_den_ne⟩

/-- Algorithm 6.3 with its exact decoder product and reconstruction proof. -/
def encodeResult (f : Frac) (hnum : f.num ≠ 0) : Encoding f :=
  if hhigh : 2 * normNat f.den ≤ normNat f.num then
    finishInitial (initialHigh f hnum hhigh)
  else
    finishInitial (initialLow f hnum (Nat.lt_of_not_ge hhigh))

/-- The raw bit word emitted by Algorithm 6.3. -/
def encode (f : Frac) (hnum : f.num ≠ 0) : Prefix.Word :=
  (encodeResult f hnum).word

/-- Public word equation for the high initial branch. -/
theorem encode_eq_high (f : Frac) (hnum : f.num ≠ 0)
    (hhigh : 2 * normNat f.den ≤ normNat f.num) :
    encode f hnum =
      (initialHigh f hnum hhigh).header ++
        (encodeTail (initialHigh f hnum hhigh).annulus).word := by
  simp [encode, encodeResult, finishInitial, hhigh]

/-- Public word equation for the low initial branch. -/
theorem encode_eq_low (f : Frac) (hnum : f.num ≠ 0)
    (hlow : normNat f.num < 2 * normNat f.den) :
    encode f hnum =
      (initialLow f hnum hlow).header ++
        (encodeTail (initialLow f hnum hlow).annulus).word := by
  have notHigh : ¬2 * normNat f.den ≤ normNat f.num := Nat.not_le.mpr hlow
  simp [encode, encodeResult, finishInitial, notHigh]

/-- Theorem 6.5, integral form: the emitted decoder product sends `ω` to the
uncancelled input numerator/denominator pair. -/
theorem encode_reconstruct_pair (f : Frac) (hnum : f.num ≠ 0) :
    (Mat2.act (encodeResult f hnum).matrix (Proj.omega : Proj GI)).Equivalent
      ⟨f.num, f.den⟩ :=
  (encodeResult f hnum).reconstruct

/-- Theorem 6.5 in the paper's Gaussian-rational affine coordinates. -/
theorem encode_reconstruct (f : Frac) (hnum : f.num ≠ 0) :
    (Mat2.act (mapMat (encodeResult f hnum).matrix)
      (Proj.omega : Proj GaussianRat)).Equivalent (Proj.affine f.value) := by
  have h := mapProj_equivalent (encodeResult f hnum).reconstruct
  rw [mapProj_act, mapProj_omega] at h
  dsimp [Proj.Equivalent, mapProj, Proj.affine] at h ⊢
  rw [mul_one]
  apply mul_right_cancel_of_ne f.den_toRat_ne
  calc
    (Mat2.act (mapMat (encodeResult f hnum).matrix)
        (Proj.omega : Proj GaussianRat)).p * toRat f.den =
        toRat f.num *
          (Mat2.act (mapMat (encodeResult f hnum).matrix)
            (Proj.omega : Proj GaussianRat)).q := h
    _ = (f.value * toRat f.den) *
          (Mat2.act (mapMat (encodeResult f hnum).matrix)
            (Proj.omega : Proj GaussianRat)).q := by rw [f.value_mul_den]
    _ = (f.value *
          (Mat2.act (mapMat (encodeResult f hnum).matrix)
            (Proj.omega : Proj GaussianRat)).q) * toRat f.den := by
      rw [GaussianRat.mul_assoc, GaussianRat.mul_comm (toRat f.den),
        ← GaussianRat.mul_assoc]

/-- Proposition 7.3, prefix part: consecutive truncations of a finite CCL word
are nested and remain prefixes of the completed word. -/
theorem encode_prefix_tower (f : Frac) (hnum : f.num ≠ 0) (n : ℕ) :
    (encode f hnum).take n <+: (encode f hnum).take (n + 1) ∧
      (encode f hnum).take n <+: encode f hnum :=
  ⟨Prefix.take_prefix_succ _ _, Prefix.take_prefix_word _ _⟩

/-- Proposition 7.3, gauge part: every proper truncation is at exactly its
cylindrical gauge radius from the completed finite word. -/
theorem encode_prefix_distance (G : Prefix.Gauge) (f : Frac) (hnum : f.num ≠ 0)
    {n : ℕ} (hn : n < (encode f hnum).length) :
    Prefix.distance G ((encode f hnum).take n) (encode f hnum) =
      G.value ((encode f hnum).take n) :=
  Prefix.distance_take_exact G _ hn

end CCLEncoder

end CCL
