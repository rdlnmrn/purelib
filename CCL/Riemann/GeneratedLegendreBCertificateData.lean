import CCL.Riemann.ExplicitLegendreLoopBaseBranches

/-!
# Compact generated data for the explicit Legendre B-period

This module is the trusted checker interface for certificate data emitted by
`scripts/generate-legendre-certificate.py`.  The Python program is not part of
the trusted build: it chooses dyadic centres, while the definitions below
reconstruct the exact B-cycle geometry and check all rational inequalities.

Entries are checked in short consecutive chunks.  This prevents a complete
certificate from becoming one large kernel reduction and keeps ordinary Lean
elaboration limits sufficient.
-/

namespace CCL.Riemann.GeneratedLegendreBCertificateData

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

open RFAP.ConstructiveGaussian.Gaussian

def point (re im : Coordinate) : Gaussian := ⟨re, im⟩

/-- A directly supplied reduced rational.  Generated dyadics use an explicit
Bézout witness so Lean never has to normalize their large denominators. -/
def reducedRational (num : Int) (den : Nat) (denPositive : 0 < den)
    (left right : Int)
    (bezout : left * (num.natAbs : Int) + right * (den : Int) = 1) :
    Coordinate where
  num := num
  den := den
  den_pos := denPositive
  reduced := ⟨⟨left, right, bezout⟩⟩

/-- The fixed Legendre parameter used by the explicit normalized example. -/
def lambda : Gaussian := point (1 / 4) 2

/-- The factored cubic used by the external generator. -/
def radicand (z : Gaussian) : Gaussian :=
  z * (z - 1) * (z - lambda)

/-- Endpoints of the four oriented raw B-cycle legs.  The two middle legs
are stationary because the displayed branch anchors have the same imaginary
coordinate; retaining them matches the canonical refined connector exactly. -/
def legStart : Nat -> Gaussian
  | 0 => point (-(1 / 2)) (-(1 / 2))
  | 1 => point (15 / 16) (-(1 / 2))
  | 2 => point (15 / 16) (-(1 / 2))
  | 3 => point (15 / 16) (-(1 / 2))
  | _ => 0

def legFinish : Nat -> Gaussian
  | 0 => point (15 / 16) (-(1 / 2))
  | 1 => point (15 / 16) (-(1 / 2))
  | 2 => point (15 / 16) (-(1 / 2))
  | 3 => point (-(1 / 2)) (-(1 / 2))
  | _ => 0

/-- One untrusted approximation row.  Geometry is deliberately absent: its
global position determines the exact cell endpoints below. -/
structure CellData where
  position : Nat
  rootCenter : Gaussian
  coefficient : Gaussian
  coefficientErrorSq : Coordinate
  deriving DecidableEq

namespace CellData

def leg (cellsPerLeg : Nat) (data : CellData) : Nat :=
  data.position / cellsPerLeg

def localIndex (cellsPerLeg : Nat) (data : CellData) : Nat :=
  data.position % cellsPerLeg

def start (cellsPerLeg : Nat) (data : CellData) : Gaussian :=
  let leg := data.leg cellsPerLeg
  let parameter : Coordinate :=
    RFAP.CanonicalFraction.fromInt (Int.ofNat (data.localIndex cellsPerLeg)) /
      RFAP.CanonicalFraction.fromInt (Int.ofNat cellsPerLeg)
  legStart leg + CCL.FiniteExp.scale parameter (legFinish leg - legStart leg)

def finish (cellsPerLeg : Nat) (data : CellData) : Gaussian :=
  let leg := data.leg cellsPerLeg
  let parameter : Coordinate :=
    RFAP.CanonicalFraction.fromInt
        (Int.ofNat (data.localIndex cellsPerLeg + 1)) /
      RFAP.CanonicalFraction.fromInt (Int.ofNat cellsPerLeg)
  legStart leg + CCL.FiniteExp.scale parameter (legFinish leg - legStart leg)

def intervalSquareLower (lower upper : Coordinate) : Coordinate :=
  if lower <= 0 ∧ 0 <= upper then 0 else min (lower ^ 2) (upper ^ 2)

def rootNormSqLower (halfWidth : Coordinate) (data : CellData) : Coordinate :=
  intervalSquareLower (data.rootCenter.re - halfWidth)
      (data.rootCenter.re + halfWidth) +
    intervalSquareLower (data.rootCenter.im - halfWidth)
      (data.rootCenter.im + halfWidth)

/-- A direct cubic expansion of `p(start + t*d) - p(start)`.  Three times
the sum of the coefficient norm-squares bounds its norm-square uniformly for
`0 <= t <= 1`. -/
def radicandVariationSq (cellsPerLeg : Nat) (data : CellData) : Coordinate :=
  let origin := data.start cellsPerLeg
  let displacement := data.finish cellsPerLeg - origin
  let cubic := displacement * displacement * displacement
  let quadratic :=
    (CCL.FiniteExp.scale 3 origin - (1 + lambda)) * displacement * displacement
  let linear :=
    (origin * CCL.FiniteExp.scale 3 origin -
        CCL.FiniteExp.scale 2 origin * (1 + lambda) + lambda) * displacement
  3 * (normSq linear + normSq quadratic + normSq cubic)

def rootResidualSq (cellsPerLeg : Nat) (data : CellData) : Coordinate :=
  normSq (data.rootCenter * data.rootCenter - radicand (data.start cellsPerLeg))

def roucheLinearSq (halfWidth : Coordinate) (data : CellData) : Coordinate :=
  4 * normSq data.rootCenter * halfWidth ^ 2

def roucheRemainderSq (cellsPerLeg : Nat) (halfWidth : Coordinate)
    (data : CellData) : Coordinate :=
  4 * (data.rootResidualSq cellsPerLeg + 4 * halfWidth ^ 4 +
    data.radicandVariationSq cellsPerLeg)

/-- Denominator-cleared reciprocal error check.  Since
`|q - 1/c|^2 = |q*c - 1|^2 / |c|^2`, multiplying the desired coefficient
bound by the positive quantity `L*|c|^2` avoids constructing large exact
reciprocals in the kernel. -/
def coefficientErrorClearedLeft (halfWidth : Coordinate)
    (data : CellData) : Coordinate :=
  data.coefficientErrorSq * data.rootNormSqLower halfWidth *
    normSq data.rootCenter

def coefficientErrorClearedRight (halfWidth : Coordinate)
    (data : CellData) : Coordinate :=
  2 * (normSq (data.coefficient * data.rootCenter - 1) *
      data.rootNormSqLower halfWidth + 2 * halfWidth ^ 2)

/-- The arithmetic contract is deliberately split into small decisions.  A
single conjunction containing all cubic and reciprocal calculations exceeds
ordinary kernel recursion depth even for one row. -/
def basicValid (cellsPerLeg : Nat) (halfWidth : Coordinate)
    (data : CellData) : Bool :=
  decide (0 < cellsPerLeg ∧ data.position < 4 * cellsPerLeg ∧ 0 < halfWidth)

def rootBoxValid (halfWidth : Coordinate) (data : CellData) : Bool :=
  decide (0 < data.rootNormSqLower halfWidth)

def roucheValid (cellsPerLeg : Nat) (halfWidth : Coordinate)
    (data : CellData) : Bool :=
  decide (data.roucheRemainderSq cellsPerLeg halfWidth <
    data.roucheLinearSq halfWidth)

def coefficientValid (halfWidth : Coordinate) (data : CellData) : Bool :=
  decide (data.coefficientErrorClearedRight halfWidth <=
    data.coefficientErrorClearedLeft halfWidth)

def overlaps (halfWidth : Coordinate) (left right : CellData) : Bool :=
  decide (|left.rootCenter.re - right.rootCenter.re| <= 2 * halfWidth ∧
    |left.rootCenter.im - right.rootCenter.im| <= 2 * halfWidth)

def contribution (cellsPerLeg : Nat) (data : CellData) : Gaussian :=
  (data.finish cellsPerLeg - data.start cellsPerLeg) * data.coefficient

def weightedAllowance (cellsPerLeg : Nat) (data : CellData) : Coordinate :=
  normSq (data.finish cellsPerLeg - data.start cellsPerLeg) *
    data.coefficientErrorSq

end CellData

/-- Check exact consecutive positions and root-box overlap inside one short
generated chunk. -/
def checkSequence (halfWidth : Coordinate) :
    Nat -> Option CellData -> List CellData -> Bool
  | _, _, [] => true
  | expected, previous, data :: remaining =>
      decide (data.position = expected) &&
        (match previous with
        | none => true
        | some prior => prior.overlaps halfWidth data) &&
        checkSequence halfWidth (expected + 1) (some data) remaining

def checkBasic (cellsPerLeg : Nat) (halfWidth : Coordinate) :
    List CellData -> Bool
  | [] => true
  | data :: remaining =>
      data.basicValid cellsPerLeg halfWidth &&
        checkBasic cellsPerLeg halfWidth remaining

def checkRootBoxes (halfWidth : Coordinate) : List CellData -> Bool
  | [] => true
  | data :: remaining =>
      data.rootBoxValid halfWidth && checkRootBoxes halfWidth remaining

def checkRouche (cellsPerLeg : Nat) (halfWidth : Coordinate) :
    List CellData -> Bool
  | [] => true
  | data :: remaining =>
      data.roucheValid cellsPerLeg halfWidth &&
        checkRouche cellsPerLeg halfWidth remaining

def checkCoefficients (halfWidth : Coordinate) : List CellData -> Bool
  | [] => true
  | data :: remaining =>
      data.coefficientValid halfWidth && checkCoefficients halfWidth remaining

/-- A bounded certificate fragment.  The only proof is evaluation of the
small checker above; complete certificates concatenate already checked
fragments rather than reevaluating their rows. -/
structure CheckedChunk (cellsPerLeg : Nat) (halfWidth : Coordinate)
    (offset : Nat) where
  entries : List CellData
  nonempty : entries ≠ []
  sequenceChecked : checkSequence halfWidth offset none entries = true
  basicChecked : checkBasic cellsPerLeg halfWidth entries = true
  rootBoxesChecked : checkRootBoxes halfWidth entries = true
  roucheChecked : checkRouche cellsPerLeg halfWidth entries = true
  coefficientsChecked : checkCoefficients halfWidth entries = true

namespace CheckedChunk

def sample {cellsPerLeg : Nat} {halfWidth : Coordinate} {offset : Nat}
    (chunk : CheckedChunk cellsPerLeg halfWidth offset) : Gaussian :=
  chunk.entries.foldr (fun data total => data.contribution cellsPerLeg + total) 0

def weightedAllowance {cellsPerLeg : Nat} {halfWidth : Coordinate}
    {offset : Nat} (chunk : CheckedChunk cellsPerLeg halfWidth offset) : Coordinate :=
  chunk.entries.foldr
    (fun data total => data.weightedAllowance cellsPerLeg + total) 0

end CheckedChunk

/-! ## Fixed-grid checker

The structures above state the rational mathematics directly.  Generated
payloads use the equivalent fixed-grid representation below so certificate
checking performs only integer arithmetic. -/

/-- Signed integer numerator over a displayed power-of-two denominator.  It
is intentionally not normalized: arithmetic stays cheap and equality/order
use cross multiplication. -/
structure Dyadic where
  numerator : Int
  bits : Nat
  deriving DecidableEq

namespace Dyadic

def ofInt (value : Int) : Dyadic := ⟨value, 0⟩

instance : Zero Dyadic := ⟨ofInt 0⟩
instance : One Dyadic := ⟨ofInt 1⟩

def add (left right : Dyadic) : Dyadic :=
  let bits := max left.bits right.bits
  { numerator := left.numerator * (2 : Int) ^ (bits - left.bits) +
      right.numerator * (2 : Int) ^ (bits - right.bits)
    bits := bits }

def neg (value : Dyadic) : Dyadic := ⟨-value.numerator, value.bits⟩

def sub (left right : Dyadic) : Dyadic := left.add right.neg

def mul (left right : Dyadic) : Dyadic :=
  ⟨left.numerator * right.numerator, left.bits + right.bits⟩

instance : Add Dyadic := ⟨add⟩
instance : Neg Dyadic := ⟨neg⟩
instance : Sub Dyadic := ⟨sub⟩
instance : Mul Dyadic := ⟨mul⟩

def scale (factor : Int) (value : Dyadic) : Dyadic :=
  ⟨factor * value.numerator, value.bits⟩

def le (left right : Dyadic) : Bool :=
  let bits := max left.bits right.bits
  decide (left.numerator * (2 : Int) ^ (bits - left.bits) <=
    right.numerator * (2 : Int) ^ (bits - right.bits))

def lt (left right : Dyadic) : Bool :=
  let bits := max left.bits right.bits
  decide (left.numerator * (2 : Int) ^ (bits - left.bits) <
    right.numerator * (2 : Int) ^ (bits - right.bits))

def min (left right : Dyadic) : Dyadic :=
  if left.le right then left else right

def square (value : Dyadic) : Dyadic := value.mul value

def toFraction (value : Dyadic) : RFAP.ConstructiveFraction.Fraction :=
  { num := value.numerator
    den := (2 : Int) ^ value.bits
    den_pos := Int.pow_pos (by decide) }

def toCoordinate (value : Dyadic) : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction value.toFraction

@[simp] theorem toCoordinate_ofInt (value : Int) :
    (ofInt value).toCoordinate = (value : Coordinate) := by
  unfold toCoordinate toFraction ofInt
  rw [RFAP.ConstructiveFraction.ofFraction_eq_div]
  change (value : Coordinate) / 1 = (value : Coordinate)
  have cancel := RFAP.ConstructiveFraction.div_mul_cancel_of_ne
    (value : Coordinate) 1 (by decide)
  rw [RFAP.ConstructiveFraction.mul_one_direct] at cancel
  exact cancel

theorem le_sound {left right : Dyadic} (checked : left.le right = true) :
    left.toCoordinate <= right.toCoordinate := by
  unfold toCoordinate
  rw [RFAP.ConstructiveFraction.ofFraction_le_iff]
  change left.numerator * (2 : Int) ^ right.bits <=
    right.numerator * (2 : Int) ^ left.bits
  unfold le at checked
  have aligned := of_decide_eq_true checked
  rcases Nat.le_total left.bits right.bits with order | order
  · simp only [max_eq_right order, Nat.sub_self, pow_zero,
      _root_.mul_one] at aligned
    have factorNonnegative : (0 : Int) <= (2 : Int) ^ left.bits :=
      Int.pow_nonneg (by decide)
    have scaled := Int.mul_le_mul_of_nonneg_right aligned
      factorNonnegative
    have powerIdentity :
        (2 : Int) ^ (right.bits - left.bits) * (2 : Int) ^ left.bits =
          (2 : Int) ^ right.bits := by
      rw [← pow_add, Nat.sub_add_cancel order]
    rw [_root_.mul_assoc, powerIdentity] at scaled
    exact scaled
  · simp only [max_eq_left order, Nat.sub_self, pow_zero,
      _root_.mul_one] at aligned
    have factorNonnegative : (0 : Int) <= (2 : Int) ^ right.bits :=
      Int.pow_nonneg (by decide)
    have scaled := Int.mul_le_mul_of_nonneg_right aligned
      factorNonnegative
    have powerIdentity :
        (2 : Int) ^ (left.bits - right.bits) * (2 : Int) ^ right.bits =
          (2 : Int) ^ left.bits := by
      rw [← pow_add, Nat.sub_add_cancel order]
    rw [_root_.mul_assoc, powerIdentity] at scaled
    exact scaled

theorem lt_sound {left right : Dyadic} (checked : left.lt right = true) :
    left.toCoordinate < right.toCoordinate := by
  unfold lt at checked
  have aligned := of_decide_eq_true checked
  have cross : left.numerator * (2 : Int) ^ right.bits <
      right.numerator * (2 : Int) ^ left.bits := by
    rcases Nat.le_total left.bits right.bits with order | order
    · simp only [max_eq_right order, Nat.sub_self, pow_zero,
        _root_.mul_one] at aligned
      have factorPositive : (0 : Int) < (2 : Int) ^ left.bits :=
        Int.pow_pos (by decide)
      have scaled := Int.mul_lt_mul_of_pos_right aligned
        factorPositive
      have powerIdentity :
          (2 : Int) ^ (right.bits - left.bits) * (2 : Int) ^ left.bits =
            (2 : Int) ^ right.bits := by
        rw [← pow_add, Nat.sub_add_cancel order]
      rw [_root_.mul_assoc, powerIdentity] at scaled
      exact scaled
    · simp only [max_eq_left order, Nat.sub_self, pow_zero,
        _root_.mul_one] at aligned
      have factorPositive : (0 : Int) < (2 : Int) ^ right.bits :=
        Int.pow_pos (by decide)
      have scaled := Int.mul_lt_mul_of_pos_right aligned
        factorPositive
      have powerIdentity :
          (2 : Int) ^ (left.bits - right.bits) * (2 : Int) ^ right.bits =
            (2 : Int) ^ left.bits := by
        rw [← pow_add, Nat.sub_add_cancel order]
      rw [_root_.mul_assoc, powerIdentity] at scaled
      exact scaled
  apply lt_of_not_ge
  intro reverse
  unfold toCoordinate at reverse
  rw [RFAP.ConstructiveFraction.ofFraction_le_iff] at reverse
  exact (not_le_of_gt cross) reverse

theorem toCoordinate_mul (left right : Dyadic) :
    (left.mul right).toCoordinate =
      left.toCoordinate * right.toCoordinate := by
  unfold toCoordinate
  rw [RFAP.ConstructiveFraction.ofFraction_mulFraction]
  apply RFAP.ConstructiveFraction.ofFraction_eq_of_equivalent
  unfold toFraction mul RFAP.ConstructiveFraction.mulFraction
    RFAP.ConstructiveFraction.Equivalent
  simp only [pow_add]

theorem toCoordinate_add (left right : Dyadic) :
    (left.add right).toCoordinate =
      left.toCoordinate + right.toCoordinate := by
  rw [show left.toCoordinate + right.toCoordinate =
      RFAP.ConstructiveFraction.ofFraction
        (RFAP.ConstructiveFraction.addFraction left.toFraction
          right.toFraction) by
    exact RFAP.ConstructiveFraction.ofFraction_addFraction _ _]
  apply RFAP.ConstructiveFraction.ofFraction_eq_of_equivalent
  unfold toFraction add RFAP.ConstructiveFraction.addFraction
    RFAP.ConstructiveFraction.Equivalent
  rcases Nat.le_total left.bits right.bits with order | order
  · rw [max_eq_right order]
    have powerIdentity :
        (2 : Int) ^ (right.bits - left.bits) * (2 : Int) ^ left.bits =
          (2 : Int) ^ right.bits := by
      rw [← pow_add, Nat.sub_add_cancel order]
    simp only [Nat.sub_self, pow_zero, _root_.mul_one]
    rw [← powerIdentity]
    ring1
  · rw [max_eq_left order]
    have powerIdentity :
        (2 : Int) ^ (left.bits - right.bits) * (2 : Int) ^ right.bits =
          (2 : Int) ^ left.bits := by
      rw [← pow_add, Nat.sub_add_cancel order]
    simp only [Nat.sub_self, pow_zero, _root_.mul_one]
    rw [← powerIdentity]
    ring1

theorem toCoordinate_neg (value : Dyadic) :
    value.neg.toCoordinate = -value.toCoordinate := by
  have denominatorPositive : (0 : Coordinate) < value.toFraction.den := by
    rw [RFAP.CanonicalFraction.intCast_eq_fromInt,
      RFAP.CanonicalFraction.zero_lt_iff_num_pos]
    exact value.toFraction.den_pos
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    denominatorPositive.ne'
  calc
    value.neg.toCoordinate * (value.toFraction.den : Coordinate) =
        ((-value.numerator : Int) : Coordinate) :=
      RFAP.ConstructiveFraction.ofFraction_mul_den _
    _ = -(value.numerator : Coordinate) := by rw [Int.cast_neg]
    _ = (-value.toCoordinate) * (value.toFraction.den : Coordinate) := by
      rw [neg_mul]
      congr 1
      unfold toCoordinate
      simpa only [toFraction] using
        (RFAP.ConstructiveFraction.ofFraction_mul_den value.toFraction).symm

theorem toCoordinate_sub (left right : Dyadic) :
    (left.sub right).toCoordinate =
      left.toCoordinate - right.toCoordinate := by
  rw [sub, toCoordinate_add, toCoordinate_neg]
  rfl

theorem toCoordinate_scale (factor : Int) (value : Dyadic) :
    (value.scale factor).toCoordinate =
      (factor : Coordinate) * value.toCoordinate := by
  have denominatorPositive : (0 : Coordinate) < value.toFraction.den := by
    rw [RFAP.CanonicalFraction.intCast_eq_fromInt,
      RFAP.CanonicalFraction.zero_lt_iff_num_pos]
    exact value.toFraction.den_pos
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    denominatorPositive.ne'
  calc
    (value.scale factor).toCoordinate *
        (value.toFraction.den : Coordinate) =
      ((factor * value.numerator : Int) : Coordinate) :=
        RFAP.ConstructiveFraction.ofFraction_mul_den _
    _ = (factor : Coordinate) * (value.numerator : Coordinate) := by
      rw [RFAP.ConstructiveFraction.intCast_mul_direct]
    _ = ((factor : Coordinate) * value.toCoordinate) *
        (value.toFraction.den : Coordinate) := by
      rw [_root_.mul_assoc]
      congr 1
      unfold toCoordinate
      simpa only [toFraction] using
        (RFAP.ConstructiveFraction.ofFraction_mul_den value.toFraction).symm

end Dyadic

structure DyadicGaussian where
  re : Dyadic
  im : Dyadic
  deriving DecidableEq

namespace DyadicGaussian

instance : Zero DyadicGaussian := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
instance : One DyadicGaussian := ⟨⟨1, 0⟩, ⟨0, 0⟩⟩

def add (left right : DyadicGaussian) : DyadicGaussian :=
  ⟨left.re.add right.re, left.im.add right.im⟩

def neg (value : DyadicGaussian) : DyadicGaussian :=
  ⟨value.re.neg, value.im.neg⟩

def sub (left right : DyadicGaussian) : DyadicGaussian := left.add right.neg

def mul (left right : DyadicGaussian) : DyadicGaussian :=
  ⟨(left.re.mul right.re).sub (left.im.mul right.im),
    (left.re.mul right.im).add (left.im.mul right.re)⟩

instance : Add DyadicGaussian := ⟨add⟩
instance : Neg DyadicGaussian := ⟨neg⟩
instance : Sub DyadicGaussian := ⟨sub⟩
instance : Mul DyadicGaussian := ⟨mul⟩

def scale (factor : Int) (value : DyadicGaussian) : DyadicGaussian :=
  ⟨value.re.scale factor, value.im.scale factor⟩

def normSq (value : DyadicGaussian) : Dyadic :=
  value.re.square.add value.im.square

def toGaussian (value : DyadicGaussian) : Gaussian :=
  ⟨value.re.toCoordinate, value.im.toCoordinate⟩

theorem toGaussian_add (left right : DyadicGaussian) :
    (left.add right).toGaussian = left.toGaussian + right.toGaussian := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [toGaussian, add, RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im, Dyadic.toCoordinate_add]

theorem toGaussian_neg (value : DyadicGaussian) :
    value.neg.toGaussian = -value.toGaussian := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [toGaussian, neg, RFAP.ConstructiveGaussian.Gaussian.neg_re,
      RFAP.ConstructiveGaussian.Gaussian.neg_im, Dyadic.toCoordinate_neg]

theorem toGaussian_sub (left right : DyadicGaussian) :
    (left.sub right).toGaussian = left.toGaussian - right.toGaussian := by
  rw [sub, toGaussian_add, toGaussian_neg]
  rfl

theorem toGaussian_mul (left right : DyadicGaussian) :
    (left.mul right).toGaussian = left.toGaussian * right.toGaussian := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [toGaussian, mul, RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im, Dyadic.toCoordinate_add,
      Dyadic.toCoordinate_sub, Dyadic.toCoordinate_mul]

theorem toGaussian_scale (factor : Int) (value : DyadicGaussian) :
    (value.scale factor).toGaussian =
      CCL.FiniteExp.scale (factor : Coordinate) value.toGaussian := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [toGaussian, scale, CCL.FiniteExp.scale,
      Dyadic.toCoordinate_scale]

theorem normSq_toGaussian (value : DyadicGaussian) :
    value.normSq.toCoordinate =
      RFAP.ConstructiveGaussian.Gaussian.normSq value.toGaussian := by
  unfold normSq Dyadic.square RFAP.ConstructiveGaussian.Gaussian.normSq
  rw [Dyadic.toCoordinate_add, Dyadic.toCoordinate_mul,
    Dyadic.toCoordinate_mul, pow_two, pow_two]
  rfl

end DyadicGaussian

/-- Compact row emitted by Python.  All three grids are global certificate
parameters, so each row stores only the integer numerators and the two root
box widths needed by the checker. -/
structure CompactCellData where
  position : Nat
  rootRe : Int
  rootIm : Int
  halfWidthBits : Nat
  transportHalfWidthBits : Nat
  coefficientRe : Int
  coefficientIm : Int
  coefficientErrorNumerator : Int
  transportCoefficientErrorNumerator : Int
  deriving DecidableEq

namespace CompactCellData

def rootCenter (rootBits : Nat) (data : CompactCellData) : DyadicGaussian :=
  ⟨⟨data.rootRe, rootBits⟩, ⟨data.rootIm, rootBits⟩⟩

def coefficient (coefficientBits : Nat)
    (data : CompactCellData) : DyadicGaussian :=
  ⟨⟨data.coefficientRe, coefficientBits⟩,
    ⟨data.coefficientIm, coefficientBits⟩⟩

def coefficientErrorSq (allowanceBits : Nat)
    (data : CompactCellData) : Dyadic :=
  ⟨data.coefficientErrorNumerator, allowanceBits⟩

/-- The same arithmetic row viewed through its transport-only root square.
The coefficient data remains attached to the narrow square and is never
read through this view. -/
def transportView (data : CompactCellData) : CompactCellData :=
  { data with
      halfWidthBits := data.transportHalfWidthBits
      coefficientErrorNumerator := data.transportCoefficientErrorNumerator }

/-- Ordinary rational half-width of the generated square root box. -/
def halfWidth (data : CompactCellData) : Coordinate :=
  (Dyadic.mk 1 data.halfWidthBits).toCoordinate

theorem dyadicUnit_positive (bits : Nat) :
    0 < (Dyadic.mk 1 bits).toCoordinate := by
  unfold Dyadic.toCoordinate Dyadic.toFraction
  rw [RFAP.ConstructiveFraction.ofFraction_eq_div]
  change (0 : Coordinate) < (1 : Coordinate) /
    (((2 : Int) ^ bits : Int) : Coordinate)
  apply RFAP.ConstructiveFraction.div_pos_direct
  · decide
  · rw [RFAP.CanonicalFraction.intCast_eq_fromInt,
      RFAP.CanonicalFraction.zero_lt_iff_num_pos]
    exact Int.pow_pos (by decide)

theorem halfWidth_positive (data : CompactCellData) :
    0 < data.halfWidth := by
  exact dyadicUnit_positive data.halfWidthBits

/-- Ordinary Gaussian interpretation of the generated root centre. -/
def rootCenterValue (rootBits : Nat) (data : CompactCellData) : Gaussian :=
  (data.rootCenter rootBits).toGaussian

/-- Ordinary Gaussian interpretation of the generated reciprocal centre. -/
def coefficientValue (coefficientBits : Nat)
    (data : CompactCellData) : Gaussian :=
  (data.coefficient coefficientBits).toGaussian

/-- The generated rational square in the root plane. -/
def rootBox (rootBits : Nat) (data : CompactCellData) : RFAP.Boxes.Box :=
  RFAP.AffineWinding.centeredSquare (data.rootCenterValue rootBits)
    data.halfWidth (data.halfWidth_positive.le)

theorem rootBox_proper (rootBits : Nat) (data : CompactCellData) :
    (data.rootBox rootBits).Proper :=
  RFAP.AffineWinding.centeredSquare_proper _ data.halfWidth_positive

/-- Ordinary rational half-width of the transport-only root square. -/
def transportHalfWidth (data : CompactCellData) : Coordinate :=
  data.transportView.halfWidth

/-- Squared reciprocal error checked on the wider transport square.  Unlike
`coefficientErrorSq`, this allowance is intended to survive subsequent
prepared subdivision while retaining the same literal coefficient. -/
def transportCoefficientErrorSq (allowanceBits : Nat)
    (data : CompactCellData) : Dyadic :=
  data.transportView.coefficientErrorSq allowanceBits

@[simp] theorem transportView_coefficientValue (coefficientBits : Nat)
    (data : CompactCellData) :
    data.transportView.coefficientValue coefficientBits =
      data.coefficientValue coefficientBits := rfl

@[simp] theorem transportView_coefficientErrorSq (allowanceBits : Nat)
    (data : CompactCellData) :
    data.transportView.coefficientErrorSq allowanceBits =
      data.transportCoefficientErrorSq allowanceBits := rfl

/-- The wider square used to carry the selected root across the prepared
edge.  It is deliberately distinct from `rootBox`, which controls the sharp
reciprocal enclosure. -/
def transportRootBox (rootBits : Nat)
    (data : CompactCellData) : RFAP.Boxes.Box :=
  data.transportView.rootBox rootBits

/-- The generated B-cycle geometry has grid `2^-13`.  Its moving legs consist
of sixteen outer and eight inner dyadic cells; each stationary raw leg is kept
once and split only by the eight-cell inner bank. -/
def geometryBits : Nat := 13

def totalCellCount : Nat := 272

def legCellCount : Nat -> Nat
  | 0 => 128
  | 1 => 8
  | 2 => 8
  | 3 => 128
  | _ => 1

def legOffset : Nat -> Nat
  | 0 => 0
  | 1 => 128
  | 2 => 136
  | 3 => 144
  | _ => totalCellCount

def legOfPosition (position : Nat) : Nat :=
  if position < 128 then 0
  else if position < 136 then 1
  else if position < 144 then 2
  else 3

def scaledPoint (re im : Int) : DyadicGaussian :=
  ⟨⟨re, geometryBits⟩, ⟨im, geometryBits⟩⟩

def legStartNumerator : Nat -> Int × Int
  | 0 => (-4096, -4096)
  | 1 => (7680, -4096)
  | 2 => (7680, -4096)
  | 3 => (7680, -4096)
  | _ => (0, 0)

def legFinishNumerator : Nat -> Int × Int
  | 0 => (7680, -4096)
  | 1 => (7680, -4096)
  | 2 => (7680, -4096)
  | 3 => (-4096, -4096)
  | _ => (0, 0)

def interpolate (start finish : Int) (cellCount localIndex : Nat) : Int :=
  start + ((finish - start) / Int.ofNat cellCount) * Int.ofNat localIndex

def start (data : CompactCellData) : DyadicGaussian :=
  let leg := legOfPosition data.position
  let localIndex := data.position - legOffset leg
  let start := legStartNumerator leg
  let finish := legFinishNumerator leg
  scaledPoint (interpolate start.1 finish.1 (legCellCount leg) localIndex)
    (interpolate start.2 finish.2 (legCellCount leg) localIndex)

def finish (data : CompactCellData) : DyadicGaussian :=
  let leg := legOfPosition data.position
  let localIndex := data.position - legOffset leg + 1
  let start := legStartNumerator leg
  let finish := legFinishNumerator leg
  scaledPoint (interpolate start.1 finish.1 (legCellCount leg) localIndex)
    (interpolate start.2 finish.2 (legCellCount leg) localIndex)

def dyadicLambda : DyadicGaussian := scaledPoint 2048 16384

def radicandAt (data : CompactCellData) : DyadicGaussian :=
  let z := data.start
  (z.mul (z.sub 1)).mul (z.sub dyadicLambda)

def rootResidualSq (rootBits : Nat) (data : CompactCellData) : Dyadic :=
  ((data.rootCenter rootBits).mul (data.rootCenter rootBits) - data.radicandAt).normSq

def radicandVariationSq (data : CompactCellData) : Dyadic :=
  let origin := data.start
  let displacement := data.finish.sub origin
  let cubic := (displacement.mul displacement).mul displacement
  let quadratic :=
    ((origin.scale 3).sub (1 + dyadicLambda)).mul
      (displacement.mul displacement)
  let linear :=
    (((origin.mul (origin.scale 3)).sub
        ((origin.scale 2).mul (1 + dyadicLambda))).add dyadicLambda).mul
      displacement
  (linear.normSq.scale 2).add
    ((quadratic.normSq.add cubic.normSq).scale 4)

def intervalSquareLower (lower upper : Dyadic) : Dyadic :=
  if lower.le 0 && (0 : Dyadic).le upper then 0
  else lower.square.min upper.square

def boxNormSqLower (center : DyadicGaussian)
    (halfWidthBits : Nat) : Dyadic :=
  let halfWidth : Dyadic := ⟨1, halfWidthBits⟩
  (intervalSquareLower (center.re.sub halfWidth) (center.re.add halfWidth)).add
    (intervalSquareLower (center.im.sub halfWidth) (center.im.add halfWidth))

def rootNormSqLower (rootBits : Nat)
    (data : CompactCellData) : Dyadic :=
  boxNormSqLower (data.rootCenter rootBits) data.halfWidthBits

/-- Coordinatewise lower bound for `|z + c|²` when `z` lies in the square
centred at the generated root centre `c`. -/
def rootSecondFactorNormSqLower (rootBits : Nat)
    (data : CompactCellData) : Dyadic :=
  boxNormSqLower ((data.rootCenter rootBits).scale 2) data.halfWidthBits

/-- Lower bound for `|(z-c)(z+c)|²` on the generated square boundary. -/
def factorizedMainSq (rootBits : Nat)
    (data : CompactCellData) : Dyadic :=
  (⟨1, data.halfWidthBits⟩ : Dyadic).square.mul
    (data.rootSecondFactorNormSqLower rootBits)

def roucheLinearSq (rootBits : Nat)
    (data : CompactCellData) : Dyadic :=
  ((data.rootCenter rootBits).normSq.mul
    ⟨1, 2 * data.halfWidthBits⟩).scale 4

def roucheRemainderSq (rootBits : Nat)
    (data : CompactCellData) : Dyadic :=
  let halfWidthFourth : Dyadic := ⟨1, 4 * data.halfWidthBits⟩
  ((data.rootResidualSq rootBits).add
      ((halfWidthFourth.scale 4).add data.radicandVariationSq)).scale 3

/-- Source-only Rouché remainder.  Unlike `roucheRemainderSq`, this does not
pay for the whole generated row: it certifies the stronger clearance at the
row's left endpoint which is subsequently spent on the actual prepared
subedge. -/
def sourceRoucheRemainderSq (rootBits : Nat)
    (data : CompactCellData) : Dyadic :=
  let halfWidthFourth : Dyadic := ⟨1, 4 * data.halfWidthBits⟩
  ((data.rootResidualSq rootBits).add
      (halfWidthFourth.scale 4)).scale 3

/-- The scan-free preparation theorem bounds its requested clearance by this
fixed dyadic value. -/
def preparationClearanceFloor : Dyadic := ⟨1, 20⟩

/-- Exact source clearance retained by the row's root square before any path
motion is charged. -/
def sourceClearanceSq (rootBits : Nat)
    (data : CompactCellData) : Dyadic :=
  (data.roucheLinearSq rootBits).sub
    (data.sourceRoucheRemainderSq rootBits)

/-- Sixteen times a direct factorized boundary-clearance bound.  The weighted
square inequality
`15 |u|² ≤ 16 |u+r|² + 240 |r|²`
keeps the useful first-order box width while charging only the tiny centre
residual.  Storing the numerator avoids dyadic division in the checker. -/
def factorizedClearanceNumerator (rootBits : Nat)
    (data : CompactCellData) : Dyadic :=
  (data.factorizedMainSq rootBits).scale 15 |>.sub
    ((data.rootResidualSq rootBits).scale 240)

def coefficientErrorClearedLeft (rootBits allowanceBits : Nat)
    (data : CompactCellData) : Dyadic :=
  ((data.coefficientErrorSq allowanceBits).mul
      (data.rootNormSqLower rootBits)).mul
    (data.rootCenter rootBits).normSq

def coefficientErrorClearedRight (rootBits coefficientBits : Nat)
    (data : CompactCellData) : Dyadic :=
  let productError :=
    ((data.coefficient coefficientBits).mul
      (data.rootCenter rootBits)).sub 1 |>.normSq
  ((productError.mul (data.rootNormSqLower rootBits)).add
      ⟨2, 2 * data.halfWidthBits⟩).scale 2

def localValid (rootBits coefficientBits allowanceBits : Nat)
    (data : CompactCellData) : Bool :=
  decide (data.position < totalCellCount) &&
    (0 : Dyadic).lt (data.rootNormSqLower rootBits) &&
    (data.roucheRemainderSq rootBits).lt
      (data.roucheLinearSq rootBits) &&
    data.radicandVariationSq.lt data.radicandAt.normSq &&
    (data.coefficientErrorClearedRight rootBits coefficientBits
      ).le
        (data.coefficientErrorClearedLeft rootBits allowanceBits)

/-- Both the sharp coefficient square and the transport-only square must be
independently valid winding-one boxes.  The latter's reciprocal estimate is
checked but never charged to the literal integration allowance. -/
def valid (rootBits coefficientBits allowanceBits : Nat)
    (data : CompactCellData) : Bool :=
  data.localValid rootBits coefficientBits allowanceBits &&
    data.transportView.localValid rootBits coefficientBits allowanceBits &&
    (preparationClearanceFloor.scale 16).le
      (data.transportView.factorizedClearanceNumerator rootBits)

/-- Ordinary rational inequalities extracted from one successful compact
row check.  The dyadic expressions are the exact expressions evaluated by
the integer checker, merely interpreted in the canonical rational field. -/
structure Bounds (rootBits coefficientBits allowanceBits : Nat)
    (data : CompactCellData) : Prop where
  positionWithin : data.position < totalCellCount
  rootNormSqLowerPositive :
    0 < (data.rootNormSqLower rootBits).toCoordinate
  rouche :
    (data.roucheRemainderSq rootBits).toCoordinate <
      (data.roucheLinearSq rootBits).toCoordinate
  radicandSeparated :
    data.radicandVariationSq.toCoordinate <
      data.radicandAt.normSq.toCoordinate
  coefficient :
    (data.coefficientErrorClearedRight rootBits coefficientBits
        ).toCoordinate <=
      (data.coefficientErrorClearedLeft rootBits allowanceBits).toCoordinate

/-- The transport-specific part of a successful compact check. -/
structure TransportBounds (rootBits coefficientBits allowanceBits : Nat)
    (data : CompactCellData) : Prop where
  rootBounds :
    data.transportView.Bounds rootBits coefficientBits allowanceBits
  clearanceFloor :
    (preparationClearanceFloor.scale 16).toCoordinate <=
      (data.transportView.factorizedClearanceNumerator rootBits).toCoordinate

theorem localValid_sound {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (checked : data.localValid rootBits coefficientBits allowanceBits = true) :
    data.Bounds rootBits coefficientBits allowanceBits := by
  unfold localValid at checked
  simp only [Bool.and_eq_true] at checked
  rcases checked with
    ⟨⟨⟨⟨positionChecked, rootChecked⟩, roucheChecked⟩,
      radicandChecked⟩, coefficientChecked⟩
  exact
    { positionWithin := of_decide_eq_true positionChecked
      rootNormSqLowerPositive := Dyadic.lt_sound rootChecked
      rouche := Dyadic.lt_sound roucheChecked
      radicandSeparated := Dyadic.lt_sound radicandChecked
      coefficient := Dyadic.le_sound coefficientChecked }

theorem valid_sound {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (checked : data.valid rootBits coefficientBits allowanceBits = true) :
    data.Bounds rootBits coefficientBits allowanceBits := by
  unfold valid at checked
  simp only [Bool.and_eq_true] at checked
  exact localValid_sound checked.1.1

theorem transportValid_sound {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (checked : data.valid rootBits coefficientBits allowanceBits = true) :
    data.TransportBounds rootBits coefficientBits allowanceBits := by
  unfold valid at checked
  simp only [Bool.and_eq_true] at checked
  exact
    { rootBounds := localValid_sound checked.1.2
      clearanceFloor := Dyadic.le_sound checked.2 }

def overlaps (rootBits : Nat)
    (left right : CompactCellData) : Bool :=
  let width : Dyadic :=
    (Dyadic.mk 1 left.halfWidthBits).add
      (Dyadic.mk 1 right.halfWidthBits)
  let realDifference :=
    (left.rootCenter rootBits).re.sub (right.rootCenter rootBits).re
  let imaginaryDifference :=
    (left.rootCenter rootBits).im.sub (right.rootCenter rootBits).im
  realDifference.le width && realDifference.neg.le width &&
    imaginaryDifference.le width && imaginaryDifference.neg.le width

/-- A deterministic narrow square centred at the next row's root centre.
The two-bit shrink leaves strict room inside either neighboring row square;
the link checker below also verifies that this square still owns one root. -/
def bridgeHalfWidthBits (left right : CompactCellData) : Nat :=
  max left.halfWidthBits right.halfWidthBits + 2

def bridgeHalfWidth (left right : CompactCellData) : Dyadic :=
  ⟨1, bridgeHalfWidthBits left right⟩

def bridgeRoucheLinearSq (rootBits : Nat)
    (left right : CompactCellData) : Dyadic :=
  ((right.rootCenter rootBits).normSq.mul
    (bridgeHalfWidth left right).square).scale 4

def bridgeRoucheRemainderSq (rootBits : Nat)
    (left right : CompactCellData) : Dyadic :=
  ((right.rootResidualSq rootBits).add
    ((bridgeHalfWidth left right).square.square.scale 4)).scale 4

/-- Fixed-grid strict containment of the link bridge in one row square. -/
def bridgeStrictInside (rootBits : Nat)
    (left right outer : CompactCellData) : Bool :=
  let center := right.rootCenter rootBits
  let width := bridgeHalfWidth left right
  let outerCenter := outer.rootCenter rootBits
  let outerWidth : Dyadic := ⟨1, outer.halfWidthBits⟩
  (outerCenter.re.sub outerWidth).lt (center.re.sub width) &&
    (center.re.add width).lt (outerCenter.re.add outerWidth) &&
    (outerCenter.im.sub outerWidth).lt (center.im.sub width) &&
    (center.im.add width).lt (outerCenter.im.add outerWidth)

/-- The semantic part of an adjacency link.  The exact path endpoints agree;
besides ordinary overlap, the deterministic bridge square is strictly inside
both rows and has winding one for the next row's start radicand. -/
def bridgeValid (rootBits : Nat)
    (left right : CompactCellData) : Bool :=
  decide (left.finish = right.start) &&
    left.overlaps rootBits right &&
    (bridgeRoucheRemainderSq rootBits left right).lt
      (bridgeRoucheLinearSq rootBits left right) &&
    bridgeStrictInside rootBits left right left &&
    bridgeStrictInside rootBits left right right

structure Overlap (rootBits : Nat)
    (left right : CompactCellData) : Prop where
  realUpper :
    ((left.rootCenter rootBits).re.sub
      (right.rootCenter rootBits).re).toCoordinate <=
        ((Dyadic.mk 1 left.halfWidthBits).add
          (Dyadic.mk 1 right.halfWidthBits)).toCoordinate
  realLower :
    (((left.rootCenter rootBits).re.sub
      (right.rootCenter rootBits).re).neg).toCoordinate <=
        ((Dyadic.mk 1 left.halfWidthBits).add
          (Dyadic.mk 1 right.halfWidthBits)).toCoordinate
  imaginaryUpper :
    ((left.rootCenter rootBits).im.sub
      (right.rootCenter rootBits).im).toCoordinate <=
        ((Dyadic.mk 1 left.halfWidthBits).add
          (Dyadic.mk 1 right.halfWidthBits)).toCoordinate
  imaginaryLower :
    (((left.rootCenter rootBits).im.sub
      (right.rootCenter rootBits).im).neg).toCoordinate <=
        ((Dyadic.mk 1 left.halfWidthBits).add
          (Dyadic.mk 1 right.halfWidthBits)).toCoordinate

theorem overlaps_sound {rootBits : Nat}
    {left right : CompactCellData}
    (checked : left.overlaps rootBits right = true) :
    Overlap rootBits left right := by
  unfold overlaps at checked
  simp only [Bool.and_eq_true] at checked
  rcases checked with ⟨⟨⟨realUpper, realLower⟩, imaginaryUpper⟩,
    imaginaryLower⟩
  exact
    { realUpper := Dyadic.le_sound realUpper
      realLower := Dyadic.le_sound realLower
      imaginaryUpper := Dyadic.le_sound imaginaryUpper
      imaginaryLower := Dyadic.le_sound imaginaryLower }

/-- Ordinary rational meaning of one successful fixed-grid bridge check. -/
structure BridgeBounds (rootBits : Nat)
    (left right : CompactCellData) : Prop where
  endpoint : left.finish.toGaussian = right.start.toGaussian
  overlap : Overlap rootBits left right
  rouche :
    (bridgeRoucheRemainderSq rootBits left right).toCoordinate <
      (bridgeRoucheLinearSq rootBits left right).toCoordinate
  strictLeft :
    let center := right.rootCenter rootBits
    let width := bridgeHalfWidth left right
    let outerCenter := left.rootCenter rootBits
    let outerWidth : Dyadic := ⟨1, left.halfWidthBits⟩
    (outerCenter.re.sub outerWidth).toCoordinate <
        (center.re.sub width).toCoordinate ∧
      (center.re.add width).toCoordinate <
        (outerCenter.re.add outerWidth).toCoordinate ∧
      (outerCenter.im.sub outerWidth).toCoordinate <
        (center.im.sub width).toCoordinate ∧
      (center.im.add width).toCoordinate <
        (outerCenter.im.add outerWidth).toCoordinate
  strictRight :
    let center := right.rootCenter rootBits
    let width := bridgeHalfWidth left right
    let outerCenter := right.rootCenter rootBits
    let outerWidth : Dyadic := ⟨1, right.halfWidthBits⟩
    (outerCenter.re.sub outerWidth).toCoordinate <
        (center.re.sub width).toCoordinate ∧
      (center.re.add width).toCoordinate <
        (outerCenter.re.add outerWidth).toCoordinate ∧
      (outerCenter.im.sub outerWidth).toCoordinate <
        (center.im.sub width).toCoordinate ∧
      (center.im.add width).toCoordinate <
        (outerCenter.im.add outerWidth).toCoordinate

theorem bridgeValid_sound {rootBits : Nat}
    {left right : CompactCellData}
    (checked : left.bridgeValid rootBits right = true) :
    BridgeBounds rootBits left right := by
  unfold bridgeValid at checked
  simp only [Bool.and_eq_true] at checked
  rcases checked with
    ⟨⟨⟨⟨endpoint, overlap⟩, rouche⟩, strictLeft⟩, strictRight⟩
  unfold bridgeStrictInside at strictLeft strictRight
  simp only [Bool.and_eq_true] at strictLeft strictRight
  rcases strictLeft with ⟨⟨⟨leftLeft, leftRight⟩, leftBottom⟩, leftTop⟩
  rcases strictRight with ⟨⟨⟨rightLeft, rightRight⟩, rightBottom⟩,
    rightTop⟩
  exact
    { endpoint := congrArg DyadicGaussian.toGaussian
        (of_decide_eq_true endpoint)
      overlap := overlaps_sound overlap
      rouche := Dyadic.lt_sound rouche
      strictLeft := ⟨Dyadic.lt_sound leftLeft, Dyadic.lt_sound leftRight,
        Dyadic.lt_sound leftBottom, Dyadic.lt_sound leftTop⟩
      strictRight := ⟨Dyadic.lt_sound rightLeft, Dyadic.lt_sound rightRight,
        Dyadic.lt_sound rightBottom, Dyadic.lt_sound rightTop⟩ }

end CompactCellData

/-- One compact row retained together with its successful local arithmetic
check.  Unlike a bare theorem name, this packages the evidence in a uniform
finite list that downstream certificate folds can consume. -/
structure CompactCheckedCell (rootBits coefficientBits allowanceBits : Nat) where
  data : CompactCellData
  checked : data.valid rootBits coefficientBits allowanceBits = true

namespace CompactCheckedCell

theorem bounds {rootBits coefficientBits allowanceBits : Nat}
    (cell : CompactCheckedCell rootBits coefficientBits allowanceBits) :
    cell.data.Bounds rootBits coefficientBits allowanceBits :=
  CompactCellData.valid_sound cell.checked

/-- Independently checked root semantics for the transport-only square. -/
theorem transportBounds {rootBits coefficientBits allowanceBits : Nat}
    (cell : CompactCheckedCell rootBits coefficientBits allowanceBits) :
    cell.data.TransportBounds rootBits coefficientBits allowanceBits :=
  CompactCellData.transportValid_sound cell.checked

end CompactCheckedCell

def checkCompactChunk (rootBits coefficientBits allowanceBits : Nat) :
    Nat -> Option CompactCellData -> List CompactCellData -> Bool
  | _, _, [] => true
  | expected, previous, data :: remaining =>
      decide (data.position = expected) &&
      data.valid rootBits coefficientBits allowanceBits &&
        (match previous with
        | none => true
        | some prior => prior.bridgeValid rootBits data) &&
        checkCompactChunk rootBits coefficientBits allowanceBits
          (expected + 1) (some data) remaining

structure CompactCheckedChunk (rootBits coefficientBits allowanceBits
    offset : Nat) where
  entries : List CompactCellData
  nonempty : entries ≠ []
  checked : checkCompactChunk rootBits coefficientBits allowanceBits
    offset none entries = true

/-! ## Shard and whole-certificate accounting

The expensive local validity calculation remains in one-row checked chunks.
The following checks contain only additions, multiplications, and comparisons
of the already displayed integers.  They can therefore certify adjacency and
exact sums in moderately sized shards without adding another deep rational
reduction to every row.
-/

/-- Fixed-grid totals for a consecutive collection of generated cells.
`sampleRe` and `sampleIm` have denominator
`2^(CompactCellData.geometryBits + coefficientBits)`; `weightedAllowance`
and `transportWeightedError` have denominator
`2^(2 * CompactCellData.geometryBits + allowanceBits)`, while `movementSq`
has denominator `2^(2 * CompactCellData.geometryBits)`. -/
structure CompactTotals where
  count : Nat
  sampleRe : Int
  sampleIm : Int
  weightedAllowance : Int
  movementSq : Int
  transportWeightedError : Int
  deriving DecidableEq

namespace CompactTotals

def zero : CompactTotals := ⟨0, 0, 0, 0, 0, 0⟩

def add (left right : CompactTotals) : CompactTotals :=
  { count := left.count + right.count
    sampleRe := left.sampleRe + right.sampleRe
    sampleIm := left.sampleIm + right.sampleIm
    weightedAllowance :=
      left.weightedAllowance + right.weightedAllowance
    movementSq := left.movementSq + right.movementSq
    transportWeightedError :=
      left.transportWeightedError + right.transportWeightedError }

def movementSqValue (totals : CompactTotals) : Coordinate :=
  (Dyadic.mk totals.movementSq (2 * CompactCellData.geometryBits)).toCoordinate

def transportWeightedErrorValue (allowanceBits : Nat)
    (totals : CompactTotals) : Coordinate :=
  (Dyadic.mk totals.transportWeightedError
    (2 * CompactCellData.geometryBits + allowanceBits)).toCoordinate

end CompactTotals

namespace CompactCellData

/-- Numerators of the exact constant-cell contribution on the common
geometry/coefficient grid. -/
def contributionNumerators (coefficientBits : Nat)
    (data : CompactCellData) : Int × Int :=
  let contribution := (data.finish.sub data.start).mul
    (data.coefficient coefficientBits)
  (contribution.re.numerator, contribution.im.numerator)

/-- Numerator of this cell's weighted semantic allowance on the common
geometry/allowance grid.  The factor four pays for comparing the generated
reciprocal centre with a freshly refined genuine quotient reading. -/
def weightedAllowanceNumerator (allowanceBits : Nat)
    (data : CompactCellData) : Int :=
  let weighted := ((data.finish.sub data.start).normSq.mul
    (data.coefficientErrorSq allowanceBits)).scale 4
  weighted.numerator

def movementSqNumerator (data : CompactCellData) : Int :=
  (data.finish.sub data.start).normSq.numerator

def transportWeightedErrorNumerator (allowanceBits : Nat)
    (data : CompactCellData) : Int :=
  ((data.finish.sub data.start).normSq.mul
    (data.transportCoefficientErrorSq allowanceBits)).numerator

def totals (coefficientBits allowanceBits : Nat)
    (data : CompactCellData) : CompactTotals :=
  let contribution := data.contributionNumerators coefficientBits
  { count := 1
    sampleRe := contribution.1
    sampleIm := contribution.2
    weightedAllowance := data.weightedAllowanceNumerator allowanceBits
    movementSq := data.movementSqNumerator
    transportWeightedError :=
      data.transportWeightedErrorNumerator allowanceBits }

end CompactCellData

/-- Tail-recursive exact totals for one generated shard. -/
def compactTotals (coefficientBits allowanceBits : Nat)
    (entries : List CompactCellData) : CompactTotals :=
  entries.foldl
    (fun total data => total.add (data.totals coefficientBits allowanceBits))
    CompactTotals.zero

/-- The cheap part of consecutive-cell validation.  Local arithmetic is
checked separately by `CompactCheckedChunk`; this pass certifies positions
and every overlap inside a generated shard. -/
def checkCompactSequence (rootBits : Nat) :
    Nat -> Option CompactCellData -> List CompactCellData -> Bool
  | _, _, [] => true
  | expected, previous, data :: remaining =>
      decide (data.position = expected) &&
        (match previous with
        | none => true
        | some prior => prior.bridgeValid rootBits data) &&
        checkCompactSequence rootBits (expected + 1)
          (some data) remaining

/-- Propositional content of the cheap consecutive-cell pass.  It exposes
the exact position and bridge evidence without asking downstream proofs to
reduce the Boolean checker again. -/
def CompactSequenceBounds (rootBits : Nat) :
    Nat -> Option CompactCellData -> List CompactCellData -> Prop
  | _, _, [] => True
  | expected, previous, data :: remaining =>
      data.position = expected ∧
        (match previous with
        | none => True
        | some prior => CompactCellData.BridgeBounds rootBits prior data) ∧
        CompactSequenceBounds rootBits (expected + 1)
          (some data) remaining

theorem checkCompactSequence_sound {rootBits expected : Nat}
    {previous : Option CompactCellData} {entries : List CompactCellData}
    (checked : checkCompactSequence rootBits expected previous entries = true) :
    CompactSequenceBounds rootBits expected previous entries := by
  induction entries generalizing expected previous with
  | nil => trivial
  | cons data remaining induction =>
      unfold checkCompactSequence at checked
      simp only [Bool.and_eq_true] at checked
      rcases checked with ⟨⟨position, bridge⟩, rest⟩
      refine ⟨of_decide_eq_true position, ?_, induction rest⟩
      cases previous with
      | none => trivial
      | some prior => exact CompactCellData.bridgeValid_sound bridge

/-- Compact, independently checked summary of one generated source module. -/
structure CompactCheckedShard (rootBits coefficientBits allowanceBits
    offset : Nat) where
  checkedCells : List
    (CompactCheckedCell rootBits coefficientBits allowanceBits)
  nonempty : checkedCells ≠ []
  firstCell : CompactCellData
  lastCell : CompactCellData
  firstChecked : (checkedCells.head nonempty).data = firstCell
  lastChecked : (checkedCells.getLast nonempty).data = lastCell
  sequenceChecked :
    checkCompactSequence rootBits offset none
      (checkedCells.map CompactCheckedCell.data) = true
  totals : CompactTotals
  totalsChecked : compactTotals coefficientBits allowanceBits
    (checkedCells.map CompactCheckedCell.data) = totals

namespace CompactCheckedShard

def first {rootBits coefficientBits allowanceBits offset : Nat}
    (shard : CompactCheckedShard rootBits coefficientBits allowanceBits
      offset) : CompactCellData :=
  shard.firstCell

def last {rootBits coefficientBits allowanceBits offset : Nat}
    (shard : CompactCheckedShard rootBits coefficientBits allowanceBits
      offset) : CompactCellData :=
  shard.lastCell

def entries {rootBits coefficientBits allowanceBits offset : Nat}
    (shard : CompactCheckedShard rootBits coefficientBits allowanceBits
      offset) : List CompactCellData :=
  shard.checkedCells.map CompactCheckedCell.data

theorem sequenceBounds
    {rootBits coefficientBits allowanceBits offset : Nat}
    (shard : CompactCheckedShard rootBits coefficientBits allowanceBits
      offset) :
    CompactSequenceBounds rootBits offset none shard.entries :=
  checkCompactSequence_sound shard.sequenceChecked

end CompactCheckedShard

/-- One actual boundary link between independently checked shards. -/
structure CompactShardLink where
  left : CompactCellData
  right : CompactCellData

def CompactShardLink.expectedRightPosition (link : CompactShardLink) : Nat :=
  if link.left.position + 1 = CompactCellData.totalCellCount then 0
  else link.left.position + 1

def CompactShardLink.valid (rootBits : Nat)
    (link : CompactShardLink) : Bool :=
  decide (link.right.position = link.expectedRightPosition) &&
    link.left.bridgeValid rootBits link.right

structure CompactShardLink.Bounds (rootBits : Nat)
    (link : CompactShardLink) : Prop where
  position : link.right.position = link.expectedRightPosition
  bridge : CompactCellData.BridgeBounds rootBits link.left link.right

theorem CompactShardLink.valid_sound {rootBits : Nat}
    {link : CompactShardLink} (checked : link.valid rootBits = true) :
    link.Bounds rootBits := by
  unfold CompactShardLink.valid at checked
  simp only [Bool.and_eq_true] at checked
  exact
    { position := of_decide_eq_true checked.1
      bridge := CompactCellData.bridgeValid_sound checked.2 }

def checkCompactShardLinks (rootBits : Nat) :
    List CompactShardLink -> Bool
  | [] => true
  | link :: remaining =>
      link.valid rootBits &&
        checkCompactShardLinks rootBits remaining

def CompactShardLinksBounds (rootBits : Nat) :
    List CompactShardLink -> Prop
  | [] => True
  | link :: remaining =>
      link.Bounds rootBits ∧ CompactShardLinksBounds rootBits remaining

theorem checkCompactShardLinks_sound {rootBits : Nat}
    {links : List CompactShardLink}
    (checked : checkCompactShardLinks rootBits links = true) :
    CompactShardLinksBounds rootBits links := by
  induction links with
  | nil => trivial
  | cons link remaining induction =>
      unfold checkCompactShardLinks at checked
      simp only [Bool.and_eq_true] at checked
      exact ⟨CompactShardLink.valid_sound checked.1, induction checked.2⟩

/-- Tail-recursive sum of the small shard summaries. -/
def compactShardTotals (totals : List CompactTotals) : CompactTotals :=
  totals.foldl CompactTotals.add CompactTotals.zero

namespace CompactTotals

def literalSample (coefficientBits : Nat)
    (totals : CompactTotals) : Gaussian :=
  DyadicGaussian.toGaussian
    ⟨⟨totals.sampleRe, CompactCellData.geometryBits + coefficientBits⟩,
      ⟨totals.sampleIm, CompactCellData.geometryBits + coefficientBits⟩⟩

def weightedAllowanceValue (allowanceBits : Nat)
    (totals : CompactTotals) : Coordinate :=
  Dyadic.toCoordinate
    ⟨totals.weightedAllowance,
      2 * CompactCellData.geometryBits + allowanceBits⟩

def aggregateAllowance (allowanceBits : Nat)
    (totals : CompactTotals) : Coordinate :=
  Dyadic.toCoordinate
    ⟨Int.ofNat totals.count * totals.weightedAllowance,
      2 * CompactCellData.geometryBits + allowanceBits⟩

end CompactTotals

def compactMovement (movementBits : Nat) (movementNumerator : Int) :
    Coordinate :=
  Dyadic.toCoordinate ⟨movementNumerator, movementBits⟩

def compactRealLower (coefficientBits movementBits : Nat)
    (totals : CompactTotals) (movementNumerator : Int) : Coordinate :=
  (totals.literalSample coefficientBits).re -
    compactMovement movementBits movementNumerator

/-- The final fixed-grid inequalities needed by the displayed real lower
bound.  This checks nonnegative allowance, that the claimed movement squares
above the complete Cauchy--Schwarz allowance, and that the real sample remains
positive after that movement. -/
def checkCompactGlobalBounds (coefficientBits allowanceBits movementBits : Nat)
    (totals : CompactTotals) (movementNumerator : Int) : Bool :=
  let sampleBits := CompactCellData.geometryBits + coefficientBits
  let weightedBits := 2 * CompactCellData.geometryBits + allowanceBits
  let weighted : Dyadic := ⟨totals.weightedAllowance, weightedBits⟩
  let aggregate : Dyadic :=
    ⟨Int.ofNat totals.count * totals.weightedAllowance, weightedBits⟩
  let movement : Dyadic := ⟨movementNumerator, movementBits⟩
  (0 : Dyadic).le weighted && (0 : Dyadic).lt movement &&
    aggregate.le movement.square &&
    movement.lt ⟨totals.sampleRe, sampleBits⟩

/-- Proposition-valued meaning of the final whole-certificate arithmetic.
This is the small trusted boundary consumed by theorem-facing clients; the
large generated integers remain behind the Boolean checker. -/
structure CompactGlobalBounds (coefficientBits allowanceBits movementBits : Nat)
    (totals : CompactTotals) (movementNumerator : Int) : Prop where
  weightedAllowanceNonnegative :
    0 <= totals.weightedAllowanceValue allowanceBits
  movementPositive : 0 < compactMovement movementBits movementNumerator
  aggregateAllowanceLe :
    totals.aggregateAllowance allowanceBits <=
      compactMovement movementBits movementNumerator ^ 2
  realLowerPositive :
    0 < compactRealLower coefficientBits movementBits totals movementNumerator

theorem checkCompactGlobalBounds_sound
    {coefficientBits allowanceBits movementBits : Nat}
    {totals : CompactTotals} {movementNumerator : Int}
    (checked : checkCompactGlobalBounds coefficientBits allowanceBits
      movementBits totals movementNumerator = true) :
    CompactGlobalBounds coefficientBits allowanceBits movementBits totals
      movementNumerator := by
  unfold checkCompactGlobalBounds at checked
  simp only [Bool.and_eq_true] at checked
  rcases checked with ⟨⟨⟨weightedNonnegative, movementPositive⟩,
    allowanceLe⟩, realSeparated⟩
  let weighted : Dyadic :=
    ⟨totals.weightedAllowance,
      2 * CompactCellData.geometryBits + allowanceBits⟩
  let aggregate : Dyadic :=
    ⟨Int.ofNat totals.count * totals.weightedAllowance,
      2 * CompactCellData.geometryBits + allowanceBits⟩
  let movement : Dyadic := ⟨movementNumerator, movementBits⟩
  have weightedNonnegative' : (0 : Coordinate) <= weighted.toCoordinate :=
    Dyadic.le_sound weightedNonnegative
  have movementPositive' : (0 : Coordinate) < movement.toCoordinate :=
    Dyadic.lt_sound movementPositive
  have allowanceLe' : aggregate.toCoordinate <=
      (movement.mul movement).toCoordinate :=
    Dyadic.le_sound allowanceLe
  have realSeparated' : movement.toCoordinate <
      (Dyadic.mk totals.sampleRe
        (CompactCellData.geometryBits + coefficientBits)).toCoordinate :=
    Dyadic.lt_sound realSeparated
  refine
    { weightedAllowanceNonnegative := ?_
      movementPositive := ?_
      aggregateAllowanceLe := ?_
      realLowerPositive := ?_ }
  · exact weightedNonnegative'
  · exact movementPositive'
  · change aggregate.toCoordinate <= movement.toCoordinate ^ 2
    rw [pow_two, ← Dyadic.toCoordinate_mul]
    exact allowanceLe'
  · exact RFAP.ConstructiveFraction.sub_pos_direct realSeparated'

end CCL.Riemann.GeneratedLegendreBCertificateData
