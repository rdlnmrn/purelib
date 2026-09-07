import FTA.AxisResultant
import FTA.SeparatedVariables

/-!
# Nonvanishing of the axis resultants

This module supplies the algebraic nonvanishing argument for the two
Sylvester determinants constructed in `FTA.AxisResultant`.  After adjoining
the Gaussian unit, the real and imaginary coordinate polynomials become
`p(T+iZ)` and its conjugate companion.  The invertible affine change
`U=T+iZ` identifies that pair with the separated-variable pair
`p(U), conjugate(p)(2T-U)`, whose resultant is nonzero.
-/

namespace FTA.AxisResultantNonzero

section

set_option quotPrecheck false

open CCL CCL.GaussianRat
open FTA.AxisResultant
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial

abbrev GaussianBivariate := Polynomial (Polynomial QI)

local notation "coordinateStep" =>
  fun (xVar yVar : Bivariate) (state : Bivariate × Bivariate) (a : QI) =>
    (state.1 * xVar - state.2 * yVar + Polynomial.C (Polynomial.C a.re),
      state.1 * yVar + state.2 * xVar + Polynomial.C (Polynomial.C a.im))

local notation "coordinatePolynomials" =>
  fun (p : GaussianPolynomial) (xVar yVar : Bivariate) =>
    p.normalize.coeffs.foldl (coordinateStep xVar yVar) (0, 0)

local notation "verticalCoordinates" =>
  fun (p : GaussianPolynomial) =>
    coordinatePolynomials p (Polynomial.C Polynomial.X) Polynomial.X

local notation "horizontalCoordinates" =>
  fun (p : GaussianPolynomial) =>
    coordinatePolynomials p Polynomial.X (Polynomial.C Polynomial.X)

local notation "verticalResultant" =>
  fun (p : GaussianPolynomial) =>
    (verticalCoordinates p).1.resultant (verticalCoordinates p).2
      (verticalCoordinates p).1.natDegree (verticalCoordinates p).2.natDegree

local notation "horizontalResultant" =>
  fun (p : GaussianPolynomial) =>
    (horizontalCoordinates p).1.resultant (horizontalCoordinates p).2
      (horizontalCoordinates p).1.natDegree (horizontalCoordinates p).2.natDegree

local notation "liftSpec" =>
  fun (p : Polynomial QI) => p.map Polynomial.C

local notation "reflectedSpec" =>
  fun (q : Polynomial QI) =>
    (liftSpec q).comp
      (Polynomial.C ((Polynomial.C 2) * Polynomial.X) - Polynomial.X)

/-- The explicit rational embedding into the coordinate model `ℚ(i)`. -/
def ratToGaussian : ℚ →+* QI where
  toFun r := GaussianRat.mk r 0
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp [GaussianRat.mul_re, GaussianRat.mul_im]

/-- The exact Gaussian unit `i`. -/
def imaginaryUnit : QI := GaussianRat.mk 0 1

@[simp] theorem ratToGaussian_re (r : ℚ) : (ratToGaussian r).re = r := rfl
@[simp] theorem ratToGaussian_im (r : ℚ) : (ratToGaussian r).im = 0 := rfl
@[simp] theorem imaginaryUnit_re : imaginaryUnit.re = 0 := rfl
@[simp] theorem imaginaryUnit_im : imaginaryUnit.im = 1 := rfl

@[simp] theorem gaussian_intCast_re (n : ℤ) : ((n : QI).re) = (n : ℚ) := by
  cases n with
  | ofNat n => simp
  | negSucc n => simp [Int.cast_negSucc]

@[simp] theorem gaussian_intCast_im (n : ℤ) : ((n : QI).im) = 0 := by
  cases n with
  | ofNat n => simp
  | negSucc n => simp [Int.cast_negSucc]

@[simp] theorem gaussian_ratCast_re (r : ℚ) : ((r : QI).re) = r := by
  have h := congrArg GaussianRat.re (map_ratCast ratToGaussian r)
  change r = (r : QI).re at h
  exact h.symm

@[simp] theorem gaussian_ratCast_im (r : ℚ) : ((r : QI).im) = 0 := by
  have h := congrArg GaussianRat.im (map_ratCast ratToGaussian r)
  change 0 = (r : QI).im at h
  exact h.symm

theorem rat_add_i_mul_im (z : QI) :
    ratToGaussian z.re + imaginaryUnit * ratToGaussian z.im = z := by
  rcases z with ⟨x, y⟩
  ext <;> simp [ratToGaussian, imaginaryUnit, GaussianRat.mul_re,
    GaussianRat.mul_im]

@[simp] theorem imaginaryUnit_sq : imaginaryUnit * imaginaryUnit = -1 := by
  ext <;> norm_num [imaginaryUnit, GaussianRat.mul_re, GaussianRat.mul_im]

/-- Gaussian conjugation as an exact coefficient-ring homomorphism. -/
def conjugation : QI →+* QI where
  toFun := GaussianRat.conj
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := by
    apply GaussianRat.ext
    · simp [GaussianRat.conj]
    · simp [GaussianRat.conj]
      ring
  map_mul' _ _ := by
    apply GaussianRat.ext
    · simp [GaussianRat.conj, GaussianRat.mul_re, GaussianRat.mul_im]
    · simp [GaussianRat.conj, GaussianRat.mul_re, GaussianRat.mul_im]
      ring

theorem conjugation_injective : Function.Injective conjugation := by
  intro z w h
  apply GaussianRat.ext
  · simpa [conjugation, GaussianRat.conj] using congrArg GaussianRat.re h
  · simpa [conjugation, GaussianRat.conj] using
      congrArg (fun u : QI => -u.im) h

theorem rat_sub_i_mul_im (z : QI) :
    ratToGaussian z.re + -(imaginaryUnit * ratToGaussian z.im) = conjugation z := by
  rcases z with ⟨x, y⟩
  ext <;> simp [ratToGaussian, imaginaryUnit, conjugation,
    GaussianRat.conj, GaussianRat.mul_re, GaussianRat.mul_im]

/-- Map both rational coefficient layers into Gaussian rationals. -/
local notation "mapCoordinates" =>
  fun (q : Bivariate) => q.map (Polynomial.mapRingHom ratToGaussian)

@[simp] theorem mapCoordinates_add (q r : Bivariate) :
    mapCoordinates (q + r) = mapCoordinates q + mapCoordinates r := by
  change (q + r).map (Polynomial.mapRingHom ratToGaussian) =
    q.map (Polynomial.mapRingHom ratToGaussian) +
      r.map (Polynomial.mapRingHom ratToGaussian)
  rw [Polynomial.map_add]

@[simp] theorem mapCoordinates_sub (q r : Bivariate) :
    mapCoordinates (q - r) = mapCoordinates q - mapCoordinates r := by
  change (q - r).map (Polynomial.mapRingHom ratToGaussian) =
    q.map (Polynomial.mapRingHom ratToGaussian) -
      r.map (Polynomial.mapRingHom ratToGaussian)
  rw [Polynomial.map_sub]

@[simp] theorem mapCoordinates_mul (q r : Bivariate) :
    mapCoordinates (q * r) = mapCoordinates q * mapCoordinates r := by
  change (q * r).map (Polynomial.mapRingHom ratToGaussian) =
    q.map (Polynomial.mapRingHom ratToGaussian) *
      r.map (Polynomial.mapRingHom ratToGaussian)
  rw [Polynomial.map_mul]

@[simp] theorem mapCoordinates_C_C (r : ℚ) :
    mapCoordinates (Polynomial.C (Polynomial.C r)) =
      Polynomial.C (Polynomial.C (r : QI)) := by
  simp

local notation "positivePart" =>
  fun (state : Bivariate × Bivariate) =>
    mapCoordinates state.1 +
      Polynomial.C (Polynomial.C imaginaryUnit) * mapCoordinates state.2

local notation "negativePart" =>
  fun (state : Bivariate × Bivariate) =>
    mapCoordinates state.1 -
      Polynomial.C (Polynomial.C imaginaryUnit) * mapCoordinates state.2

private theorem positive_ring_identity
    {R : Type*} [CommRing R] (I A B X Y ca cb : R)
    (hI : I * I = -1) :
    (A * X - B * Y + ca) + I * (A * Y + B * X + cb) =
      (A + I * B) * (X + I * Y) + (ca + I * cb) := by
  linear_combination -(B * Y) * hI

private theorem negative_ring_identity
    {R : Type*} [CommRing R] (I A B X Y ca cb : R)
    (hI : I * I = -1) :
    (A * X - B * Y + ca) - I * (A * Y + B * X + cb) =
      (A - I * B) * (X - I * Y) + (ca - I * cb) := by
  linear_combination -(B * Y) * hI

private theorem positivePart_coordinateStep
    (xVar yVar : Bivariate) (state : Bivariate × Bivariate) (a : QI) :
    positivePart (coordinateStep xVar yVar state a) =
      positivePart state *
          (mapCoordinates xVar +
            Polynomial.C (Polynomial.C imaginaryUnit) * mapCoordinates yVar) +
        Polynomial.C (Polynomial.C a) := by
  let I : GaussianBivariate := Polynomial.C (Polynomial.C imaginaryUnit)
  let A := mapCoordinates state.1
  let B := mapCoordinates state.2
  let X := mapCoordinates xVar
  let Y := mapCoordinates yVar
  let ca : GaussianBivariate := Polynomial.C (Polynomial.C (a.re : QI))
  let cb : GaussianBivariate := Polynomial.C (Polynomial.C (a.im : QI))
  have hI : I * I = -1 := by
    dsimp only [I]
    rw [← Polynomial.C_mul, ← Polynomial.C_mul, imaginaryUnit_sq]
    simp
  have hconstant : ca + I * cb = Polynomial.C (Polynomial.C a) := by
    dsimp only [ca, cb, I]
    rw [← Polynomial.C_mul, ← Polynomial.C_mul, ← Polynomial.C_add,
      ← Polynomial.C_add]
    congr 2
    simpa using rat_add_i_mul_im a
  dsimp only
  simp only [mapCoordinates_add,
    mapCoordinates_sub, mapCoordinates_mul, mapCoordinates_C_C]
  change (A * X - B * Y + ca) + I * (A * Y + B * X + cb) =
    (A + I * B) * (X + I * Y) + Polynomial.C (Polynomial.C a)
  calc
    _ = (A + I * B) * (X + I * Y) + (ca + I * cb) :=
      positive_ring_identity I A B X Y ca cb hI
    _ = _ := by rw [hconstant]

private theorem negativePart_coordinateStep
    (xVar yVar : Bivariate) (state : Bivariate × Bivariate) (a : QI) :
    negativePart (coordinateStep xVar yVar state a) =
      negativePart state *
          (mapCoordinates xVar -
            Polynomial.C (Polynomial.C imaginaryUnit) * mapCoordinates yVar) +
        Polynomial.C (Polynomial.C (conjugation a)) := by
  let I : GaussianBivariate := Polynomial.C (Polynomial.C imaginaryUnit)
  let A := mapCoordinates state.1
  let B := mapCoordinates state.2
  let X := mapCoordinates xVar
  let Y := mapCoordinates yVar
  let ca : GaussianBivariate := Polynomial.C (Polynomial.C (a.re : QI))
  let cb : GaussianBivariate := Polynomial.C (Polynomial.C (a.im : QI))
  have hI : I * I = -1 := by
    dsimp only [I]
    rw [← Polynomial.C_mul, ← Polynomial.C_mul, imaginaryUnit_sq]
    simp
  have hconstant : ca - I * cb =
      Polynomial.C (Polynomial.C (conjugation a)) := by
    dsimp only [ca, cb, I]
    change Polynomial.C (Polynomial.C (a.re : QI)) +
        -(Polynomial.C (Polynomial.C imaginaryUnit) *
          Polynomial.C (Polynomial.C (a.im : QI))) = _
    rw [← Polynomial.C_mul, ← Polynomial.C_mul,
      ← Polynomial.C_neg, ← Polynomial.C_neg, ← Polynomial.C_add,
      ← Polynomial.C_add]
    congr 2
    simpa using rat_sub_i_mul_im a
  dsimp only
  simp only [mapCoordinates_add,
    mapCoordinates_sub, mapCoordinates_mul, mapCoordinates_C_C]
  change (A * X - B * Y + ca) - I * (A * Y + B * X + cb) =
    (A - I * B) * (X - I * Y) +
      Polynomial.C (Polynomial.C (conjugation a))
  calc
    _ = (A - I * B) * (X - I * Y) + (ca - I * cb) :=
      negative_ring_identity I A B X Y ca cb hI
    _ = _ := by rw [hconstant]

private theorem positivePart_coordinateFold
    (xVar yVar : Bivariate) (cs : List QI)
    (state : Bivariate × Bivariate) :
    positivePart (cs.foldl (coordinateStep xVar yVar) state) =
      cs.foldl
        (fun value a => value *
            (mapCoordinates xVar +
              Polynomial.C (Polynomial.C imaginaryUnit) * mapCoordinates yVar) +
          Polynomial.C (Polynomial.C a))
        (positivePart state) := by
  induction cs generalizing state with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      have h := ih (coordinateStep xVar yVar state a)
      rw [positivePart_coordinateStep] at h
      exact h

private theorem negativePart_coordinateFold
    (xVar yVar : Bivariate) (cs : List QI)
    (state : Bivariate × Bivariate) :
    negativePart (cs.foldl (coordinateStep xVar yVar) state) =
      cs.foldl
        (fun value a => value *
            (mapCoordinates xVar -
              Polynomial.C (Polynomial.C imaginaryUnit) * mapCoordinates yVar) +
          Polynomial.C (Polynomial.C (conjugation a)))
        (negativePart state) := by
  induction cs generalizing state with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      have h := ih (coordinateStep xVar yVar state a)
      rw [negativePart_coordinateStep] at h
      exact h

private theorem lift_horner_fold_comp (cs : List QI)
    (acc : Polynomial QI) (z : GaussianBivariate) :
    (liftSpec
        (cs.foldl (fun value a => value * Polynomial.X + Polynomial.C a) acc)).comp z =
      cs.foldl
        (fun value a => value * z + Polynomial.C (Polynomial.C a))
        ((liftSpec acc).comp z) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      simp [Polynomial.map_add,
        Polynomial.map_mul, Polynomial.map_C, Polynomial.add_comp,
        Polynomial.mul_comp]

private theorem lift_toPolynomial_comp (cs : List QI) (z : GaussianBivariate) :
    (liftSpec
        (DensePolynomial.toPolynomial (DensePolynomial.mk cs))).comp z =
      cs.foldl
        (fun value a => value * z + Polynomial.C (Polynomial.C a)) 0 := by
  rw [DensePolynomial.toPolynomial_eq_foldl_horner]
  simpa using lift_horner_fold_comp cs 0 z

private theorem lift_conjugate_horner_fold_comp (cs : List QI)
    (acc : Polynomial QI) (z : GaussianBivariate) :
    (liftSpec
        ((cs.foldl
          (fun value a => value * Polynomial.X + Polynomial.C a) acc).map
            conjugation)).comp z =
      cs.foldl
        (fun value a => value * z +
          Polynomial.C (Polynomial.C (conjugation a)))
        ((liftSpec (acc.map conjugation)).comp z) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      simp [Polynomial.map_add,
        Polynomial.map_mul, Polynomial.map_C, Polynomial.add_comp,
        Polynomial.mul_comp]

private theorem lift_conjugate_toPolynomial_comp
    (cs : List QI) (z : GaussianBivariate) :
    (liftSpec
        ((DensePolynomial.toPolynomial (DensePolynomial.mk cs)).map
          conjugation)).comp z =
      cs.foldl
        (fun value a => value * z +
          Polynomial.C (Polynomial.C (conjugation a))) 0 := by
  rw [DensePolynomial.toPolynomial_eq_foldl_horner]
  simpa using lift_conjugate_horner_fold_comp cs 0 z

local notation "verticalAffine" =>
  (Polynomial.C Polynomial.X +
    Polynomial.C (Polynomial.C imaginaryUnit) * Polynomial.X : GaussianBivariate)

local notation "verticalConjugateAffine" =>
  (Polynomial.C Polynomial.X -
    Polynomial.C (Polynomial.C imaginaryUnit) * Polynomial.X : GaussianBivariate)

theorem positivePart_verticalCoordinates (p : GaussianPolynomial) :
    positivePart (verticalCoordinates p) =
      (liftSpec p.toPolynomial).comp verticalAffine := by
  have hfold := positivePart_coordinateFold
    (Polynomial.C Polynomial.X) Polynomial.X p.normalize.coeffs (0, 0)
  have hlift := lift_toPolynomial_comp p.normalize.coeffs verticalAffine
  change (liftSpec p.normalize.toPolynomial).comp
      verticalAffine = _ at hlift
  rw [toPolynomial_normalize] at hlift
  calc
    positivePart
        (p.normalize.coeffs.foldl
          (coordinateStep (Polynomial.C Polynomial.X) Polynomial.X) (0, 0)) =
      p.normalize.coeffs.foldl
        (fun value a => value * verticalAffine +
          Polynomial.C (Polynomial.C a)) 0 := by
            simpa using hfold
    _ = (liftSpec p.toPolynomial).comp verticalAffine :=
      hlift.symm

theorem negativePart_verticalCoordinates (p : GaussianPolynomial) :
    negativePart (verticalCoordinates p) =
      (liftSpec (p.toPolynomial.map conjugation)).comp
        verticalConjugateAffine := by
  have hfold := negativePart_coordinateFold
    (Polynomial.C Polynomial.X) Polynomial.X p.normalize.coeffs (0, 0)
  have hlift := lift_conjugate_toPolynomial_comp
    p.normalize.coeffs verticalConjugateAffine
  change (liftSpec
      (p.normalize.toPolynomial.map conjugation)).comp
        verticalConjugateAffine = _ at hlift
  rw [toPolynomial_normalize] at hlift
  calc
    negativePart
        (p.normalize.coeffs.foldl
          (coordinateStep (Polynomial.C Polynomial.X) Polynomial.X) (0, 0)) =
      p.normalize.coeffs.foldl
        (fun value a => value * verticalConjugateAffine +
          Polynomial.C (Polynomial.C (conjugation a))) 0 := by
            simpa using hfold
    _ = (liftSpec
        (p.toPolynomial.map conjugation)).comp verticalConjugateAffine :=
      hlift.symm

local notation "horizontalAffine" =>
  (Polynomial.X +
    Polynomial.C (Polynomial.C imaginaryUnit) * Polynomial.C Polynomial.X :
      GaussianBivariate)

local notation "horizontalConjugateAffine" =>
  (Polynomial.X -
    Polynomial.C (Polynomial.C imaginaryUnit) * Polynomial.C Polynomial.X :
      GaussianBivariate)

theorem positivePart_horizontalCoordinates (p : GaussianPolynomial) :
    positivePart (horizontalCoordinates p) =
      (liftSpec p.toPolynomial).comp horizontalAffine := by
  have hfold := positivePart_coordinateFold
    Polynomial.X (Polynomial.C Polynomial.X) p.normalize.coeffs (0, 0)
  have hlift := lift_toPolynomial_comp p.normalize.coeffs horizontalAffine
  change (liftSpec p.normalize.toPolynomial).comp
      horizontalAffine = _ at hlift
  rw [toPolynomial_normalize] at hlift
  calc
    positivePart
        (p.normalize.coeffs.foldl
          (coordinateStep Polynomial.X (Polynomial.C Polynomial.X)) (0, 0)) =
      p.normalize.coeffs.foldl
        (fun value a => value * horizontalAffine +
          Polynomial.C (Polynomial.C a)) 0 := by
            simpa using hfold
    _ = (liftSpec p.toPolynomial).comp horizontalAffine :=
      hlift.symm

theorem negativePart_horizontalCoordinates (p : GaussianPolynomial) :
    negativePart (horizontalCoordinates p) =
      (liftSpec (p.toPolynomial.map conjugation)).comp
        horizontalConjugateAffine := by
  have hfold := negativePart_coordinateFold
    Polynomial.X (Polynomial.C Polynomial.X) p.normalize.coeffs (0, 0)
  have hlift := lift_conjugate_toPolynomial_comp
    p.normalize.coeffs horizontalConjugateAffine
  change (liftSpec
      (p.normalize.toPolynomial.map conjugation)).comp
        horizontalConjugateAffine = _ at hlift
  rw [toPolynomial_normalize] at hlift
  calc
    negativePart
        (p.normalize.coeffs.foldl
          (coordinateStep Polynomial.X (Polynomial.C Polynomial.X)) (0, 0)) =
      p.normalize.coeffs.foldl
        (fun value a => value * horizontalConjugateAffine +
          Polynomial.C (Polynomial.C (conjugation a))) 0 := by
            simpa using hfold
    _ = (liftSpec
        (p.toPolynomial.map conjugation)).comp horizontalConjugateAffine :=
      hlift.symm

theorem reflected_comp_verticalAffine (q : Polynomial QI) :
    (reflectedSpec q).comp verticalAffine =
      (liftSpec q).comp verticalConjugateAffine := by
  change ((liftSpec q).comp
      (Polynomial.C (Polynomial.C 2 * Polynomial.X) - Polynomial.X)).comp
      verticalAffine = (liftSpec q).comp verticalConjugateAffine
  rw [Polynomial.comp_assoc]
  congr 1
  have htwoInner :
      Polynomial.C (2 : QI) * Polynomial.X - Polynomial.X =
        Polynomial.X := by
    have hCtwo : Polynomial.C (2 : QI) = (2 : Polynomial QI) :=
      map_ofNat Polynomial.C 2
    rw [hCtwo]
    ring
  simp
  rw [sub_add_eq_sub_sub, ← Polynomial.C_mul, ← Polynomial.C_sub, htwoInner]

/-! ## Transport through the parameter fraction field -/

abbrev GaussianParameter := Polynomial QI
abbrev GaussianFraction := FractionRing GaussianParameter

local notation "parameterEmbedding" =>
  (algebraMap GaussianParameter GaussianFraction :
    GaussianParameter →+* GaussianFraction)

theorem parameterEmbedding_injective : Function.Injective parameterEmbedding :=
  FaithfulSMul.algebraMap_injective GaussianParameter GaussianFraction

local notation "rationalParameterEmbedding" =>
  ((parameterEmbedding).comp (Polynomial.mapRingHom ratToGaussian) :
    Polynomial ℚ →+* GaussianFraction)

theorem ratToGaussian_injective : Function.Injective ratToGaussian := by
  intro x y h
  simpa using congrArg GaussianRat.re h

theorem rationalParameterEmbedding_injective :
    Function.Injective rationalParameterEmbedding := by
  intro f g h
  apply Polynomial.map_injective ratToGaussian ratToGaussian_injective
  apply parameterEmbedding_injective
  exact h

/-- Scale the parameter variable by `i`; its inverse scales by `-i`. -/
local notation "scaleParameter" =>
  (Polynomial.compRingHom
    (Polynomial.C imaginaryUnit * Polynomial.X : GaussianParameter))

local notation "unscaleParameter" =>
  (Polynomial.compRingHom
    (Polynomial.C (-imaginaryUnit) * Polynomial.X : GaussianParameter))

@[simp] theorem scaleParameter_C (a : QI) :
    scaleParameter (Polynomial.C a) = Polynomial.C a := by
  change (Polynomial.C a).comp
    (Polynomial.C imaginaryUnit * Polynomial.X) = Polynomial.C a
  simp

@[simp] theorem scaleParameter_X :
    scaleParameter Polynomial.X =
      Polynomial.C imaginaryUnit * Polynomial.X := by
  change Polynomial.X.comp
    (Polynomial.C imaginaryUnit * Polynomial.X) = _
  simp

@[simp] theorem unscaleParameter_C (a : QI) :
    unscaleParameter (Polynomial.C a) = Polynomial.C a := by
  change (Polynomial.C a).comp
    (Polynomial.C (-imaginaryUnit) * Polynomial.X) = Polynomial.C a
  simp

@[simp] theorem unscaleParameter_X :
    unscaleParameter Polynomial.X =
      Polynomial.C (-imaginaryUnit) * Polynomial.X := by
  change Polynomial.X.comp
    (Polynomial.C (-imaginaryUnit) * Polynomial.X) = _
  simp

theorem unscale_scaleParameter (q : GaussianParameter) :
    unscaleParameter (scaleParameter q) = q := by
  change (q.comp (Polynomial.C imaginaryUnit * Polynomial.X)).comp
      (Polynomial.C (-imaginaryUnit) * Polynomial.X) = q
  rw [Polynomial.comp_assoc]
  have hi : imaginaryUnit * -imaginaryUnit = 1 := by
    rw [mul_neg, imaginaryUnit_sq, _root_.neg_neg]
  have hinner :
      (Polynomial.C imaginaryUnit * Polynomial.X).comp
          (Polynomial.C (-imaginaryUnit) * Polynomial.X) = Polynomial.X := by
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
    rw [← _root_.mul_assoc, ← Polynomial.C_mul, hi]
    simp
  rw [hinner, Polynomial.comp_X]

theorem scaleParameter_injective : Function.Injective scaleParameter := by
  intro f g h
  have := congrArg unscaleParameter h
  simpa only [unscale_scaleParameter] using this

local notation "horizontalParameterEmbedding" =>
  ((parameterEmbedding).comp scaleParameter :
    GaussianParameter →+* GaussianFraction)

theorem horizontalParameterEmbedding_injective :
    Function.Injective horizontalParameterEmbedding :=
  parameterEmbedding_injective.comp scaleParameter_injective

private theorem map_scale_lift (q : Polynomial QI) :
    (liftSpec q).map scaleParameter =
      liftSpec q := by
  change (q.map Polynomial.C).map scaleParameter = q.map Polynomial.C
  rw [Polynomial.map_map]
  apply congrArg (fun φ : QI →+* GaussianParameter => q.map φ)
  apply RingHom.ext
  intro a
  exact scaleParameter_C a

private theorem lift_comp (q r : Polynomial QI) :
    liftSpec (q.comp r) =
      (liftSpec q).comp
        (liftSpec r) := by
  exact Polynomial.map_comp Polynomial.C q r

theorem scaled_reflected_comp_horizontalAffine (q : Polynomial QI) :
    ((reflectedSpec (q.comp (-Polynomial.X))).map
        scaleParameter).comp horizontalAffine =
      (liftSpec q).comp horizontalConjugateAffine := by
  change (((liftSpec (q.comp (-Polynomial.X))).comp
      (Polynomial.C (Polynomial.C 2 * Polynomial.X) - Polynomial.X)).map
        scaleParameter).comp horizontalAffine = _
  rw [Polynomial.map_comp, map_scale_lift, Polynomial.comp_assoc]
  have hargument :
      ((Polynomial.C ((Polynomial.C (2 : QI)) * Polynomial.X) -
          Polynomial.X : GaussianBivariate).map scaleParameter).comp
          horizontalAffine = -horizontalConjugateAffine := by
    have hCtwo : Polynomial.C (2 : QI) = (2 : Polynomial QI) :=
      map_ofNat Polynomial.C 2
    have hscaleTwoX :
        scaleParameter ((2 : Polynomial QI) * Polynomial.X) =
          (2 : Polynomial QI) *
            (Polynomial.C imaginaryUnit * Polynomial.X) := by
      rw [map_mul, map_ofNat, scaleParameter_X]
    simp only [Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X,
      Polynomial.C_comp, Polynomial.sub_comp, Polynomial.X_comp]
    rw [hCtwo, hscaleTwoX]
    simp
    have hOuterCtwo :
        Polynomial.C (2 : Polynomial QI) = (2 : GaussianBivariate) :=
      map_ofNat Polynomial.C 2
    rw [hOuterCtwo]
    ring
  rw [hargument, lift_comp, Polynomial.comp_assoc]
  congr 1
  simp

private theorem isCoprime_components_of_parts
    {R : Type*} [CommRing R] (A B I : R)
    (hparts : IsCoprime (A + I * B) (A - I * B)) :
    IsCoprime A B := by
  rcases hparts with ⟨u, v, huv⟩
  refine ⟨u + v, (u - v) * I, ?_⟩
  linear_combination huv

theorem isCoprime_mapped_vertical_parts
    (p : GaussianPolynomial) (hp : p.isZero = false)
    (hdegree : 0 < p.natDegree) :
    IsCoprime
      ((positivePart (verticalCoordinates p)).map parameterEmbedding)
      ((negativePart (verticalCoordinates p)).map parameterEmbedding) := by
  let f := p.toPolynomial
  let q := f.map conjugation
  have hf : f ≠ 0 := toPolynomial_ne_zero_of_isZero_false hp
  have hfDegree : f.natDegree = p.natDegree := natDegree_toPolynomial hp
  have hqDegree : 0 < q.natDegree := by
    dsimp only [q]
    rw [Polynomial.natDegree_map_eq_of_injective conjugation_injective,
      hfDegree]
    exact hdegree
  have hseparated := FTA.SeparatedVariables.isCoprime_map_lift_reflected
    parameterEmbedding parameterEmbedding_injective f q hf hqDegree
  have hchanged := hseparated.map
    (Polynomial.compRingHom ((verticalAffine).map parameterEmbedding))
  change IsCoprime
    (((liftSpec f).map parameterEmbedding).comp
      ((verticalAffine).map parameterEmbedding))
    (((reflectedSpec q).map parameterEmbedding).comp
      ((verticalAffine).map parameterEmbedding)) at hchanged
  rw [← Polynomial.map_comp, ← Polynomial.map_comp] at hchanged
  rw [reflected_comp_verticalAffine] at hchanged
  change IsCoprime
    (((liftSpec f).comp verticalAffine).map
      parameterEmbedding)
    (((liftSpec q).comp verticalConjugateAffine).map
      parameterEmbedding) at hchanged
  simpa only [f, q, ← positivePart_verticalCoordinates,
    ← negativePart_verticalCoordinates] using hchanged

theorem isCoprime_mapped_verticalCoordinates
    (p : GaussianPolynomial) (hp : p.isZero = false)
    (hdegree : 0 < p.natDegree) :
    IsCoprime
      ((verticalCoordinates p).1.map rationalParameterEmbedding)
      ((verticalCoordinates p).2.map rationalParameterEmbedding) := by
  have hparts := isCoprime_mapped_vertical_parts p hp hdegree
  have hcomponents := isCoprime_components_of_parts
    ((mapCoordinates (verticalCoordinates p).1).map parameterEmbedding)
    ((mapCoordinates (verticalCoordinates p).2).map parameterEmbedding)
    (Polynomial.C (parameterEmbedding (Polynomial.C imaginaryUnit)))
    (by
      simpa [Polynomial.map_add,
        Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C] using hparts)
  simpa [Polynomial.map_map] using
    hcomponents

theorem verticalResultant_ne_zero
    (p : GaussianPolynomial) (hp : p.isZero = false)
    (hdegree : 0 < p.natDegree) :
    verticalResultant p ≠ 0 := by
  let A := (verticalCoordinates p).1
  let B := (verticalCoordinates p).2
  have hcoprime := isCoprime_mapped_verticalCoordinates p hp hdegree
  have hmappedResultant :
      (A.map rationalParameterEmbedding).resultant
        (B.map rationalParameterEmbedding) ≠ 0 :=
    FTA.FiniteResultant.resultant_ne_zero_of_isCoprime _ _ hcoprime
  have hADegree : (A.map rationalParameterEmbedding).natDegree = A.natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      rationalParameterEmbedding_injective A
  have hBDegree : (B.map rationalParameterEmbedding).natDegree = B.natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      rationalParameterEmbedding_injective B
  have hmap := Polynomial.resultant_map_map A B A.natDegree B.natDegree
    rationalParameterEmbedding
  have hmapDefault :
      (A.map rationalParameterEmbedding).resultant
          (B.map rationalParameterEmbedding) =
        rationalParameterEmbedding (verticalResultant p) := by
    simpa only [hADegree, hBDegree, A, B] using hmap
  intro hzero
  apply hmappedResultant
  rw [hmapDefault, hzero, map_zero]

theorem isCoprime_mapped_horizontal_parts
    (p : GaussianPolynomial) (hp : p.isZero = false)
    (hdegree : 0 < p.natDegree) :
    IsCoprime
      ((positivePart (horizontalCoordinates p)).map parameterEmbedding)
      ((negativePart (horizontalCoordinates p)).map parameterEmbedding) := by
  let f := p.toPolynomial
  let q := f.map conjugation
  let qNeg := q.comp (-Polynomial.X)
  have hf : f ≠ 0 := toPolynomial_ne_zero_of_isZero_false hp
  have hfDegree : f.natDegree = p.natDegree := natDegree_toPolynomial hp
  have hqDegree : 0 < q.natDegree := by
    dsimp only [q]
    rw [Polynomial.natDegree_map_eq_of_injective conjugation_injective,
      hfDegree]
    exact hdegree
  have hqNegDegree : 0 < qNeg.natDegree := by
    dsimp only [qNeg]
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_neg,
      Polynomial.natDegree_X, _root_.mul_one]
    exact hqDegree
  have hseparated := FTA.SeparatedVariables.isCoprime_map_lift_reflected
    horizontalParameterEmbedding horizontalParameterEmbedding_injective
    f qNeg hf hqNegDegree
  have hchanged := hseparated.map
    (Polynomial.compRingHom ((horizontalAffine).map parameterEmbedding))
  change IsCoprime
    (((liftSpec f).map horizontalParameterEmbedding).comp
      ((horizontalAffine).map parameterEmbedding))
    (((reflectedSpec qNeg).map
        horizontalParameterEmbedding).comp
      ((horizontalAffine).map parameterEmbedding)) at hchanged
  have hfirst :
      ((liftSpec f).map
          horizontalParameterEmbedding).comp
          ((horizontalAffine).map parameterEmbedding) =
        ((liftSpec f).comp horizontalAffine).map
          parameterEmbedding := by
    change ((liftSpec f).map
        ((parameterEmbedding).comp scaleParameter)).comp
        ((horizontalAffine).map parameterEmbedding) = _
    rw [← Polynomial.map_map, map_scale_lift, ← Polynomial.map_comp]
  have hsecond :
      ((reflectedSpec qNeg).map
          horizontalParameterEmbedding).comp
          ((horizontalAffine).map parameterEmbedding) =
        ((liftSpec q).comp
          horizontalConjugateAffine).map parameterEmbedding := by
    change ((reflectedSpec qNeg).map
        ((parameterEmbedding).comp scaleParameter)).comp
        ((horizontalAffine).map parameterEmbedding) = _
    rw [← Polynomial.map_map, ← Polynomial.map_comp]
    exact congrArg (Polynomial.map parameterEmbedding)
      (scaled_reflected_comp_horizontalAffine q)
  rw [hfirst, hsecond] at hchanged
  simpa only [f, q, ← positivePart_horizontalCoordinates,
    ← negativePart_horizontalCoordinates] using hchanged

theorem isCoprime_mapped_horizontalCoordinates
    (p : GaussianPolynomial) (hp : p.isZero = false)
    (hdegree : 0 < p.natDegree) :
    IsCoprime
      ((horizontalCoordinates p).1.map rationalParameterEmbedding)
      ((horizontalCoordinates p).2.map rationalParameterEmbedding) := by
  have hparts := isCoprime_mapped_horizontal_parts p hp hdegree
  have hcomponents := isCoprime_components_of_parts
    ((mapCoordinates (horizontalCoordinates p).1).map parameterEmbedding)
    ((mapCoordinates (horizontalCoordinates p).2).map parameterEmbedding)
    (Polynomial.C (parameterEmbedding (Polynomial.C imaginaryUnit)))
    (by
      simpa [Polynomial.map_add,
        Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C] using hparts)
  simpa [Polynomial.map_map] using
    hcomponents

theorem horizontalResultant_ne_zero
    (p : GaussianPolynomial) (hp : p.isZero = false)
    (hdegree : 0 < p.natDegree) :
    horizontalResultant p ≠ 0 := by
  let A := (horizontalCoordinates p).1
  let B := (horizontalCoordinates p).2
  have hcoprime := isCoprime_mapped_horizontalCoordinates p hp hdegree
  have hmappedResultant :
      (A.map rationalParameterEmbedding).resultant
        (B.map rationalParameterEmbedding) ≠ 0 :=
    FTA.FiniteResultant.resultant_ne_zero_of_isCoprime _ _ hcoprime
  have hADegree : (A.map rationalParameterEmbedding).natDegree = A.natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      rationalParameterEmbedding_injective A
  have hBDegree : (B.map rationalParameterEmbedding).natDegree = B.natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      rationalParameterEmbedding_injective B
  have hmap := Polynomial.resultant_map_map A B A.natDegree B.natDegree
    rationalParameterEmbedding
  have hmapDefault :
      (A.map rationalParameterEmbedding).resultant
          (B.map rationalParameterEmbedding) =
        rationalParameterEmbedding (horizontalResultant p) := by
    simpa only [hADegree, hBDegree, A, B] using hmap
  intro hzero
  apply hmappedResultant
  rw [hmapDefault, hzero, map_zero]

/-! ## Closed certificate constructors -/

/-- Once the finite determinant program supplies dense polynomials with the
two exact specification equalities, nonvanishing follows from the algebra
above and need not be carried as additional input data. -/
def denseAxisResultantsOfSpecifications
    (p : GaussianPolynomial) (hp : p.isZero = false)
    (hdegree : 0 < p.natDegree)
    (vertical horizontal : RatPolynomial)
    (vertical_spec : vertical.toPolynomial = verticalResultant p)
    (horizontal_spec : horizontal.toPolynomial = horizontalResultant p) :
    DenseAxisResultants p where
  vertical := vertical
  horizontal := horizontal
  vertical_spec := vertical_spec
  horizontal_spec := horizontal_spec
  vertical_nonzero := verticalResultant_ne_zero p hp hdegree
  horizontal_nonzero := horizontalResultant_ne_zero p hp hdegree

/-- End-to-end bridge from two computed dense Sylvester outputs to the exact
elimination certificate consumed by all four bounded Newton-band searches. -/
def axisEliminationCertificateOfSpecifications
    (p : GaussianPolynomial) (hp : p.isZero = false)
    (hdegree : 0 < p.natDegree)
    (vertical horizontal : RatPolynomial)
    (vertical_spec : vertical.toPolynomial = verticalResultant p)
    (horizontal_spec : horizontal.toPolynomial = horizontalResultant p) :
    FTA.AxisSafeCuts.AxisEliminationCertificate p
      (2 * p.natDegree ^ 2) :=
  (denseAxisResultantsOfSpecifications p hp hdegree vertical horizontal
    vertical_spec horizontal_spec).toEliminationCertificate hp hdegree

end

end FTA.AxisResultantNonzero
