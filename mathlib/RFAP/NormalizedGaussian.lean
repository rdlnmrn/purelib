import mathlib.RFAP.ConstructiveGaussian
import mathlib.RFAP.NormalizedFraction

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace RFAP.NormalizedGaussian

abbrev Rational := RFAP.ConstructiveFraction.Rational
abbrev ReducedFraction := RFAP.ConstructiveFraction.ReducedFraction
abbrev SemanticGaussian := RFAP.ConstructiveGaussian.Gaussian

open RFAP.ConstructiveGaussian.Gaussian

/-- Two independently reduced rational coordinates. -/
abbrev Gaussian := SemanticGaussian

/-- Compatibility names for the two canonical working coordinates. -/
abbrev Gaussian.re : Gaussian → ReducedFraction :=
  RFAP.ConstructiveGaussian.Gaussian.re

abbrev Gaussian.im : Gaussian → ReducedFraction :=
  RFAP.ConstructiveGaussian.Gaussian.im

/-- Erase a normalized working pair to the existing Gaussian semantic type. -/
def value (source : Gaussian) : SemanticGaussian :=
  source

/-- Normalize both coordinates of an existing semantic Gaussian value. -/
def ofGaussian (source : SemanticGaussian) : Gaussian :=
  source

theorem value_ofGaussian (source : SemanticGaussian) :
    value (ofGaussian source) = source := rfl

theorem ofGaussian_value (source : Gaussian) :
    ofGaussian (value source) = source := rfl

def add (left right : Gaussian) : Gaussian :=
  left + right

def neg (source : Gaussian) : Gaussian :=
  -source

def sub (left right : Gaussian) : Gaussian :=
  left - right

def mul (left right : Gaussian) : Gaussian :=
  left * right

/-- Squared norm calculated entirely in the normalized scalar layer. -/
def normSq (source : Gaussian) : ReducedFraction :=
  RFAP.CanonicalGaussian.Gaussian.normSq source

/-- Total reciprocal matching the existing zero-to-zero convention. -/
def inv (source : Gaussian) : Gaussian :=
  source⁻¹

def div (left right : Gaussian) : Gaussian :=
  left / right

theorem value_add (left right : Gaussian) :
    value (add left right) = value left + value right := rfl

theorem value_neg (source : Gaussian) :
    value (neg source) = -value source := rfl

theorem value_sub (left right : Gaussian) :
    value (sub left right) = value left - value right := rfl

theorem value_mul (left right : Gaussian) :
    value (mul left right) = value left * value right := rfl

theorem value_normSq (source : Gaussian) :
    RFAP.NormalizedFraction.value (normSq source) =
      RFAP.ConstructiveGaussian.Gaussian.normSq (value source) := by
  exact (RFAP.ConstructiveGaussian.Gaussian.normSq_eq_canonical source).symm

theorem value_inv (source : Gaussian) :
    value (inv source) = (value source)⁻¹ := rfl

theorem value_div (left right : Gaussian) :
    value (div left right) = value left / value right := rfl

/-! ## Component envelopes -/

/-- Largest numerator/denominator magnitude among both reduced coordinates. -/
def componentMagnitude (source : Gaussian) : Nat :=
  max (RFAP.NormalizedFraction.componentMagnitude source.re)
    (RFAP.NormalizedFraction.componentMagnitude source.im)

theorem realMagnitude_le (source : Gaussian) :
    RFAP.NormalizedFraction.componentMagnitude source.re ≤
      componentMagnitude source :=
  le_max_left _ _

theorem imaginaryMagnitude_le (source : Gaussian) :
    RFAP.NormalizedFraction.componentMagnitude source.im ≤
      componentMagnitude source :=
  le_max_right _ _

def addMagnitudeEnvelope (left right : Nat) : Nat :=
  RFAP.NormalizedFraction.additiveMagnitudeEnvelope left right

def mulMagnitudeEnvelope (left right : Nat) : Nat :=
  let product :=
    RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope left right
  RFAP.NormalizedFraction.additiveMagnitudeEnvelope product product

def normSqMagnitudeEnvelope (source : Nat) : Nat :=
  let square :=
    RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope source source
  RFAP.NormalizedFraction.additiveMagnitudeEnvelope square square

def invMagnitudeEnvelope (source : Nat) : Nat :=
  RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope source
    (normSqMagnitudeEnvelope source)

def divMagnitudeEnvelope (left right : Nat) : Nat :=
  mulMagnitudeEnvelope left (invMagnitudeEnvelope right)

theorem addMagnitudeEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    addMagnitudeEnvelope left right ≤
      addMagnitudeEnvelope leftBound rightBound :=
  RFAP.NormalizedFraction.additiveMagnitudeEnvelope_mono leftLe rightLe

theorem mulMagnitudeEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    mulMagnitudeEnvelope left right ≤
      mulMagnitudeEnvelope leftBound rightBound := by
  unfold mulMagnitudeEnvelope
  let product :=
    RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope left right
  let productBound :=
    RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope
      leftBound rightBound
  have productLe : product ≤ productBound :=
    RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
      leftLe rightLe
  exact RFAP.NormalizedFraction.additiveMagnitudeEnvelope_mono
    productLe productLe

theorem normSqMagnitudeEnvelope_mono {source bound : Nat}
    (sourceLe : source ≤ bound) :
    normSqMagnitudeEnvelope source ≤ normSqMagnitudeEnvelope bound := by
  unfold normSqMagnitudeEnvelope
  have squareLe := RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
    sourceLe sourceLe
  exact RFAP.NormalizedFraction.additiveMagnitudeEnvelope_mono
    squareLe squareLe

theorem invMagnitudeEnvelope_mono {source bound : Nat}
    (sourceLe : source ≤ bound) :
    invMagnitudeEnvelope source ≤ invMagnitudeEnvelope bound := by
  unfold invMagnitudeEnvelope
  exact RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
    sourceLe (normSqMagnitudeEnvelope_mono sourceLe)

theorem divMagnitudeEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    divMagnitudeEnvelope left right ≤
      divMagnitudeEnvelope leftBound rightBound := by
  unfold divMagnitudeEnvelope
  exact mulMagnitudeEnvelope_mono leftLe (invMagnitudeEnvelope_mono rightLe)

theorem componentMagnitude_add_le (left right : Gaussian) :
    componentMagnitude (add left right) ≤
      addMagnitudeEnvelope (componentMagnitude left)
        (componentMagnitude right) := by
  apply max_le
  · exact (RFAP.NormalizedFraction.componentMagnitude_add_le
      left.re right.re).trans
        (RFAP.NormalizedFraction.additiveMagnitudeEnvelope_mono
          (realMagnitude_le left) (realMagnitude_le right))
  · exact (RFAP.NormalizedFraction.componentMagnitude_add_le
      left.im right.im).trans
        (RFAP.NormalizedFraction.additiveMagnitudeEnvelope_mono
          (imaginaryMagnitude_le left) (imaginaryMagnitude_le right))

theorem componentMagnitude_neg_le (source : Gaussian) :
    componentMagnitude (neg source) ≤ componentMagnitude source := by
  apply max_le
  · exact (RFAP.NormalizedFraction.componentMagnitude_neg_le source.re).trans
      (realMagnitude_le source)
  · exact (RFAP.NormalizedFraction.componentMagnitude_neg_le source.im).trans
      (imaginaryMagnitude_le source)

theorem componentMagnitude_sub_le (left right : Gaussian) :
    componentMagnitude (sub left right) ≤
      addMagnitudeEnvelope (componentMagnitude left)
        (componentMagnitude right) := by
  exact (componentMagnitude_add_le left (neg right)).trans
    (RFAP.NormalizedFraction.additiveMagnitudeEnvelope_mono (le_refl _)
      (componentMagnitude_neg_le right))

theorem componentMagnitude_mul_le (left right : Gaussian) :
    componentMagnitude (mul left right) ≤
      mulMagnitudeEnvelope (componentMagnitude left)
        (componentMagnitude right) := by
  let product := RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope
    (componentMagnitude left) (componentMagnitude right)
  have realLeft : RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.mul left.re right.re) ≤ product :=
    (RFAP.NormalizedFraction.componentMagnitude_mul_le left.re right.re).trans
      (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
        (realMagnitude_le left) (realMagnitude_le right))
  have realRight : RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.mul left.im right.im) ≤ product :=
    (RFAP.NormalizedFraction.componentMagnitude_mul_le left.im right.im).trans
      (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
        (imaginaryMagnitude_le left) (imaginaryMagnitude_le right))
  have imaginaryLeft : RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.mul left.re right.im) ≤ product :=
    (RFAP.NormalizedFraction.componentMagnitude_mul_le left.re right.im).trans
      (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
        (realMagnitude_le left) (imaginaryMagnitude_le right))
  have imaginaryRight : RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.mul left.im right.re) ≤ product :=
    (RFAP.NormalizedFraction.componentMagnitude_mul_le left.im right.re).trans
      (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
        (imaginaryMagnitude_le left) (realMagnitude_le right))
  apply max_le
  · exact (RFAP.NormalizedFraction.componentMagnitude_sub_le _ _).trans
      (RFAP.NormalizedFraction.additiveMagnitudeEnvelope_mono
        realLeft realRight)
  · exact (RFAP.NormalizedFraction.componentMagnitude_add_le _ _).trans
      (RFAP.NormalizedFraction.additiveMagnitudeEnvelope_mono
        imaginaryLeft imaginaryRight)

theorem componentMagnitude_normSq_le (source : Gaussian) :
    RFAP.NormalizedFraction.componentMagnitude (normSq source) ≤
      normSqMagnitudeEnvelope (componentMagnitude source) := by
  let square := RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope
    (componentMagnitude source) (componentMagnitude source)
  have realSquare : RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.mul source.re source.re) ≤ square :=
    (RFAP.NormalizedFraction.componentMagnitude_mul_le source.re source.re).trans
      (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
        (realMagnitude_le source) (realMagnitude_le source))
  have imaginarySquare : RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.mul source.im source.im) ≤ square :=
    (RFAP.NormalizedFraction.componentMagnitude_mul_le source.im source.im).trans
      (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
        (imaginaryMagnitude_le source) (imaginaryMagnitude_le source))
  exact (RFAP.NormalizedFraction.componentMagnitude_add_le _ _).trans
    (RFAP.NormalizedFraction.additiveMagnitudeEnvelope_mono
      realSquare imaginarySquare)

theorem componentMagnitude_inv_le (source : Gaussian) :
    componentMagnitude (inv source) ≤
      invMagnitudeEnvelope (componentMagnitude source) := by
  have denominatorBound := componentMagnitude_normSq_le source
  apply max_le
  · exact (RFAP.NormalizedFraction.componentMagnitude_div_le _ _).trans
      (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
        (realMagnitude_le source) denominatorBound)
  · exact (RFAP.NormalizedFraction.componentMagnitude_div_le _ _).trans
      (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
        ((RFAP.NormalizedFraction.componentMagnitude_neg_le source.im).trans
          (imaginaryMagnitude_le source)) denominatorBound)

theorem componentMagnitude_div_le (left right : Gaussian) :
    componentMagnitude (div left right) ≤
      divMagnitudeEnvelope (componentMagnitude left)
        (componentMagnitude right) := by
  exact (componentMagnitude_mul_le left (inv right)).trans
    (by
      unfold divMagnitudeEnvelope
      let leftMagnitude := componentMagnitude left
      let inverseMagnitude := componentMagnitude (inv right)
      let inverseBound := invMagnitudeEnvelope (componentMagnitude right)
      let product := RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope
        leftMagnitude inverseMagnitude
      let productBound := RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope
        leftMagnitude inverseBound
      apply RFAP.NormalizedFraction.additiveMagnitudeEnvelope_mono
      · exact RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
          (le_refl _) (componentMagnitude_inv_le right)
      · exact RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
          (le_refl _) (componentMagnitude_inv_le right))

/-! ## Arithmetic-step envelopes -/

def addSteps (left right : Gaussian) : Nat :=
  RFAP.NormalizedFraction.addSteps left.re right.re +
    RFAP.NormalizedFraction.addSteps left.im right.im

def negSteps (source : Gaussian) : Nat :=
  RFAP.NormalizedFraction.negSteps source.re +
    RFAP.NormalizedFraction.negSteps source.im

def subSteps (left right : Gaussian) : Nat :=
  negSteps right + addSteps left (neg right)

def mulSteps (left right : Gaussian) : Nat :=
  let realLeft := RFAP.NormalizedFraction.mul left.re right.re
  let realRight := RFAP.NormalizedFraction.mul left.im right.im
  let imaginaryLeft := RFAP.NormalizedFraction.mul left.re right.im
  let imaginaryRight := RFAP.NormalizedFraction.mul left.im right.re
  RFAP.NormalizedFraction.mulSteps left.re right.re +
    RFAP.NormalizedFraction.mulSteps left.im right.im +
    RFAP.NormalizedFraction.mulSteps left.re right.im +
    RFAP.NormalizedFraction.mulSteps left.im right.re +
    RFAP.NormalizedFraction.subSteps realLeft realRight +
    RFAP.NormalizedFraction.addSteps imaginaryLeft imaginaryRight

def normSqSteps (source : Gaussian) : Nat :=
  let realSquare := RFAP.NormalizedFraction.mul source.re source.re
  let imaginarySquare := RFAP.NormalizedFraction.mul source.im source.im
  RFAP.NormalizedFraction.mulSteps source.re source.re +
    RFAP.NormalizedFraction.mulSteps source.im source.im +
    RFAP.NormalizedFraction.addSteps realSquare imaginarySquare

def invSteps (source : Gaussian) : Nat :=
  let denominator := normSq source
  normSqSteps source +
    RFAP.NormalizedFraction.divSteps source.re denominator +
    RFAP.NormalizedFraction.negSteps source.im +
    RFAP.NormalizedFraction.divSteps
      (RFAP.NormalizedFraction.neg source.im) denominator

def divSteps (left right : Gaussian) : Nat :=
  invSteps right + mulSteps left (inv right)

def addStepEnvelope (left right : Nat) : Nat :=
  RFAP.NormalizedFraction.addStepEnvelope left right +
    RFAP.NormalizedFraction.addStepEnvelope left right

def negStepEnvelope (source : Nat) : Nat :=
  RFAP.NormalizedFraction.negStepEnvelope source +
    RFAP.NormalizedFraction.negStepEnvelope source

def subStepEnvelope (left right : Nat) : Nat :=
  negStepEnvelope right + addStepEnvelope left right

def mulStepEnvelope (left right : Nat) : Nat :=
  let product :=
    RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope left right
  RFAP.NormalizedFraction.mulStepEnvelope left right +
    RFAP.NormalizedFraction.mulStepEnvelope left right +
    RFAP.NormalizedFraction.mulStepEnvelope left right +
    RFAP.NormalizedFraction.mulStepEnvelope left right +
    RFAP.NormalizedFraction.subStepEnvelope product product +
    RFAP.NormalizedFraction.addStepEnvelope product product

def normSqStepEnvelope (source : Nat) : Nat :=
  let square :=
    RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope source source
  RFAP.NormalizedFraction.mulStepEnvelope source source +
    RFAP.NormalizedFraction.mulStepEnvelope source source +
    RFAP.NormalizedFraction.addStepEnvelope square square

def invStepEnvelope (source : Nat) : Nat :=
  let normBound := normSqMagnitudeEnvelope source
  normSqStepEnvelope source +
    RFAP.NormalizedFraction.divStepEnvelope source normBound +
    RFAP.NormalizedFraction.negStepEnvelope source +
    RFAP.NormalizedFraction.divStepEnvelope source normBound

def divStepEnvelope (left right : Nat) : Nat :=
  invStepEnvelope right + mulStepEnvelope left (invMagnitudeEnvelope right)

theorem addStepEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    addStepEnvelope left right ≤ addStepEnvelope leftBound rightBound :=
  Nat.add_le_add
    (RFAP.NormalizedFraction.addStepEnvelope_mono leftLe rightLe)
    (RFAP.NormalizedFraction.addStepEnvelope_mono leftLe rightLe)

theorem mulStepEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    mulStepEnvelope left right ≤ mulStepEnvelope leftBound rightBound := by
  let product :=
    RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope left right
  let productBound :=
    RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope
      leftBound rightBound
  have scalar := RFAP.NormalizedFraction.mulStepEnvelope_mono leftLe rightLe
  have productLe : product ≤ productBound :=
    RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
      leftLe rightLe
  have subtraction := RFAP.NormalizedFraction.subStepEnvelope_mono
    productLe productLe
  have addition := RFAP.NormalizedFraction.addStepEnvelope_mono
    productLe productLe
  unfold mulStepEnvelope
  dsimp only [product, productBound] at scalar subtraction addition ⊢
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add scalar scalar)
          scalar)
        scalar)
      subtraction)
    addition

theorem negStepEnvelope_mono {source bound : Nat} (sourceLe : source ≤ bound) :
    negStepEnvelope source ≤ negStepEnvelope bound :=
  Nat.add_le_add
    (RFAP.NormalizedFraction.negStepEnvelope_mono sourceLe)
    (RFAP.NormalizedFraction.negStepEnvelope_mono sourceLe)

theorem subStepEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    subStepEnvelope left right ≤ subStepEnvelope leftBound rightBound := by
  unfold subStepEnvelope
  exact Nat.add_le_add (negStepEnvelope_mono rightLe)
    (addStepEnvelope_mono leftLe rightLe)

theorem normSqStepEnvelope_mono {source bound : Nat}
    (sourceLe : source ≤ bound) :
    normSqStepEnvelope source ≤ normSqStepEnvelope bound := by
  let square :=
    RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope source source
  let squareBound :=
    RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope bound bound
  have multiplication := RFAP.NormalizedFraction.mulStepEnvelope_mono
    sourceLe sourceLe
  have squareLe : square ≤ squareBound :=
    RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
      sourceLe sourceLe
  have addition := RFAP.NormalizedFraction.addStepEnvelope_mono
    squareLe squareLe
  unfold normSqStepEnvelope
  dsimp only [square, squareBound] at multiplication addition ⊢
  exact Nat.add_le_add
    (Nat.add_le_add multiplication multiplication)
    addition

theorem invStepEnvelope_mono {source bound : Nat} (sourceLe : source ≤ bound) :
    invStepEnvelope source ≤ invStepEnvelope bound := by
  let normBound := normSqMagnitudeEnvelope source
  let largerNormBound := normSqMagnitudeEnvelope bound
  have normLe : normBound ≤ largerNormBound :=
    normSqMagnitudeEnvelope_mono sourceLe
  have normSteps := normSqStepEnvelope_mono sourceLe
  have division := RFAP.NormalizedFraction.divStepEnvelope_mono
    sourceLe normLe
  have negation := RFAP.NormalizedFraction.negStepEnvelope_mono sourceLe
  unfold invStepEnvelope
  dsimp only [normBound, largerNormBound] at normSteps division negation ⊢
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add normSteps division)
      negation)
    division

theorem divStepEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    divStepEnvelope left right ≤ divStepEnvelope leftBound rightBound := by
  unfold divStepEnvelope
  exact Nat.add_le_add (invStepEnvelope_mono rightLe)
    (mulStepEnvelope_mono leftLe (invMagnitudeEnvelope_mono rightLe))

theorem addSteps_le_envelope (left right : Gaussian) :
    addSteps left right ≤
      addStepEnvelope (componentMagnitude left)
        (componentMagnitude right) := by
  unfold addSteps addStepEnvelope
  exact Nat.add_le_add
    ((RFAP.NormalizedFraction.addSteps_le_envelope left.re right.re).trans
      (RFAP.NormalizedFraction.addStepEnvelope_mono
        (realMagnitude_le left) (realMagnitude_le right)))
    ((RFAP.NormalizedFraction.addSteps_le_envelope left.im right.im).trans
      (RFAP.NormalizedFraction.addStepEnvelope_mono
        (imaginaryMagnitude_le left) (imaginaryMagnitude_le right)))

theorem negSteps_le_envelope (source : Gaussian) :
    negSteps source ≤ negStepEnvelope (componentMagnitude source) := by
  unfold negSteps negStepEnvelope
  exact Nat.add_le_add
    ((RFAP.NormalizedFraction.negSteps_le_envelope source.re).trans
      (RFAP.NormalizedFraction.negStepEnvelope_mono
        (realMagnitude_le source)))
    ((RFAP.NormalizedFraction.negSteps_le_envelope source.im).trans
      (RFAP.NormalizedFraction.negStepEnvelope_mono
        (imaginaryMagnitude_le source)))

theorem subSteps_le_envelope (left right : Gaussian) :
    subSteps left right ≤
      subStepEnvelope (componentMagnitude left)
        (componentMagnitude right) := by
  have negBound := negSteps_le_envelope right
  have addBound := addSteps_le_envelope left (neg right)
  have addEnvelopeBound := addStepEnvelope_mono
    (left := componentMagnitude left)
    (right := componentMagnitude (neg right))
    (leftBound := componentMagnitude left)
    (rightBound := componentMagnitude right)
    (le_refl _) (componentMagnitude_neg_le right)
  unfold subSteps subStepEnvelope
  exact Nat.add_le_add negBound (addBound.trans addEnvelopeBound)

theorem mulSteps_le_envelope (left right : Gaussian) :
    mulSteps left right ≤
      mulStepEnvelope (componentMagnitude left)
        (componentMagnitude right) := by
  let product := RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope
    (componentMagnitude left) (componentMagnitude right)
  let realLeft := RFAP.NormalizedFraction.mul left.re right.re
  let realRight := RFAP.NormalizedFraction.mul left.im right.im
  let imaginaryLeft := RFAP.NormalizedFraction.mul left.re right.im
  let imaginaryRight := RFAP.NormalizedFraction.mul left.im right.re
  have realLeftMagnitude : RFAP.NormalizedFraction.componentMagnitude
      realLeft ≤ product :=
    (RFAP.NormalizedFraction.componentMagnitude_mul_le left.re right.re).trans
      (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
        (realMagnitude_le left) (realMagnitude_le right))
  have realRightMagnitude : RFAP.NormalizedFraction.componentMagnitude
      realRight ≤ product :=
    (RFAP.NormalizedFraction.componentMagnitude_mul_le left.im right.im).trans
      (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
        (imaginaryMagnitude_le left) (imaginaryMagnitude_le right))
  have imaginaryLeftMagnitude : RFAP.NormalizedFraction.componentMagnitude
      imaginaryLeft ≤ product :=
    (RFAP.NormalizedFraction.componentMagnitude_mul_le left.re right.im).trans
      (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
        (realMagnitude_le left) (imaginaryMagnitude_le right))
  have imaginaryRightMagnitude : RFAP.NormalizedFraction.componentMagnitude
      imaginaryRight ≤ product :=
    (RFAP.NormalizedFraction.componentMagnitude_mul_le left.im right.re).trans
      (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
        (imaginaryMagnitude_le left) (realMagnitude_le right))
  have first := (RFAP.NormalizedFraction.mulSteps_le_envelope
    left.re right.re).trans
      (RFAP.NormalizedFraction.mulStepEnvelope_mono
        (realMagnitude_le left) (realMagnitude_le right))
  have second := (RFAP.NormalizedFraction.mulSteps_le_envelope
    left.im right.im).trans
      (RFAP.NormalizedFraction.mulStepEnvelope_mono
        (imaginaryMagnitude_le left) (imaginaryMagnitude_le right))
  have third := (RFAP.NormalizedFraction.mulSteps_le_envelope
    left.re right.im).trans
      (RFAP.NormalizedFraction.mulStepEnvelope_mono
        (realMagnitude_le left) (imaginaryMagnitude_le right))
  have fourth := (RFAP.NormalizedFraction.mulSteps_le_envelope
    left.im right.re).trans
      (RFAP.NormalizedFraction.mulStepEnvelope_mono
        (imaginaryMagnitude_le left) (realMagnitude_le right))
  have fifth := (RFAP.NormalizedFraction.subSteps_le_envelope
    realLeft realRight).trans
      (RFAP.NormalizedFraction.subStepEnvelope_mono
        realLeftMagnitude realRightMagnitude)
  have sixth := (RFAP.NormalizedFraction.addSteps_le_envelope
    imaginaryLeft imaginaryRight).trans
      (RFAP.NormalizedFraction.addStepEnvelope_mono
        imaginaryLeftMagnitude imaginaryRightMagnitude)
  unfold mulSteps mulStepEnvelope
  dsimp only [realLeft, realRight, imaginaryLeft, imaginaryRight, product]
    at first second third fourth fifth sixth ⊢
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add first second)
          third)
        fourth)
      fifth)
    sixth

theorem normSqSteps_le_envelope (source : Gaussian) :
    normSqSteps source ≤ normSqStepEnvelope (componentMagnitude source) := by
  let square := RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope
    (componentMagnitude source) (componentMagnitude source)
  let realSquare := RFAP.NormalizedFraction.mul source.re source.re
  let imaginarySquare := RFAP.NormalizedFraction.mul source.im source.im
  have realMagnitude : RFAP.NormalizedFraction.componentMagnitude
      realSquare ≤ square :=
    (RFAP.NormalizedFraction.componentMagnitude_mul_le source.re source.re).trans
      (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
        (realMagnitude_le source) (realMagnitude_le source))
  have imaginaryMagnitude : RFAP.NormalizedFraction.componentMagnitude
      imaginarySquare ≤ square :=
    (RFAP.NormalizedFraction.componentMagnitude_mul_le source.im source.im).trans
      (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono
        (imaginaryMagnitude_le source) (imaginaryMagnitude_le source))
  have first := (RFAP.NormalizedFraction.mulSteps_le_envelope
    source.re source.re).trans
      (RFAP.NormalizedFraction.mulStepEnvelope_mono
        (realMagnitude_le source) (realMagnitude_le source))
  have second := (RFAP.NormalizedFraction.mulSteps_le_envelope
    source.im source.im).trans
      (RFAP.NormalizedFraction.mulStepEnvelope_mono
        (imaginaryMagnitude_le source) (imaginaryMagnitude_le source))
  have third := (RFAP.NormalizedFraction.addSteps_le_envelope
    realSquare imaginarySquare).trans
      (RFAP.NormalizedFraction.addStepEnvelope_mono
        realMagnitude imaginaryMagnitude)
  unfold normSqSteps normSqStepEnvelope
  dsimp only [realSquare, imaginarySquare, square]
    at first second third ⊢
  exact Nat.add_le_add (Nat.add_le_add first second) third

theorem invSteps_le_envelope (source : Gaussian) :
    invSteps source ≤ invStepEnvelope (componentMagnitude source) := by
  let denominator := normSq source
  let normBound := normSqMagnitudeEnvelope (componentMagnitude source)
  have denominatorMagnitude : RFAP.NormalizedFraction.componentMagnitude
      denominator ≤ normBound := componentMagnitude_normSq_le source
  have normStepsBound := normSqSteps_le_envelope source
  have realDivision := (RFAP.NormalizedFraction.divSteps_le_envelope
    source.re denominator).trans
      (RFAP.NormalizedFraction.divStepEnvelope_mono
        (realMagnitude_le source) denominatorMagnitude)
  have negation := (RFAP.NormalizedFraction.negSteps_le_envelope
    source.im).trans
      (RFAP.NormalizedFraction.negStepEnvelope_mono
        (imaginaryMagnitude_le source))
  have imaginaryDivision := (RFAP.NormalizedFraction.divSteps_le_envelope
    (RFAP.NormalizedFraction.neg source.im) denominator).trans
      (RFAP.NormalizedFraction.divStepEnvelope_mono
        ((RFAP.NormalizedFraction.componentMagnitude_neg_le source.im).trans
          (imaginaryMagnitude_le source)) denominatorMagnitude)
  have combined := Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add normStepsBound realDivision) negation)
    imaginaryDivision
  simpa only [invSteps, invStepEnvelope, denominator, normBound] using combined

theorem divSteps_le_envelope (left right : Gaussian) :
    divSteps left right ≤
      divStepEnvelope (componentMagnitude left)
        (componentMagnitude right) := by
  have inverseSteps := invSteps_le_envelope right
  have multiplication := (mulSteps_le_envelope left (inv right)).trans
    (mulStepEnvelope_mono
      (left := componentMagnitude left)
      (right := componentMagnitude (inv right))
      (leftBound := componentMagnitude left)
      (rightBound := invMagnitudeEnvelope (componentMagnitude right))
      (le_refl _) (componentMagnitude_inv_le right))
  unfold divSteps divStepEnvelope
  exact Nat.add_le_add inverseSteps multiplication

/-! ## Semantic entry points -/

def normalizedAdd (left right : SemanticGaussian) : SemanticGaussian :=
  value (add (ofGaussian left) (ofGaussian right))

def normalizedNeg (source : SemanticGaussian) : SemanticGaussian :=
  value (neg (ofGaussian source))

def normalizedSub (left right : SemanticGaussian) : SemanticGaussian :=
  value (sub (ofGaussian left) (ofGaussian right))

def normalizedMul (left right : SemanticGaussian) : SemanticGaussian :=
  value (mul (ofGaussian left) (ofGaussian right))

def normalizedInv (source : SemanticGaussian) : SemanticGaussian :=
  value (inv (ofGaussian source))

def normalizedDiv (left right : SemanticGaussian) : SemanticGaussian :=
  value (div (ofGaussian left) (ofGaussian right))

@[simp] theorem normalizedAdd_eq (left right : SemanticGaussian) :
    normalizedAdd left right = left + right := by
  rw [normalizedAdd, value_add, value_ofGaussian, value_ofGaussian]

@[simp] theorem normalizedNeg_eq (source : SemanticGaussian) :
    normalizedNeg source = -source := by
  rw [normalizedNeg, value_neg, value_ofGaussian]

@[simp] theorem normalizedSub_eq (left right : SemanticGaussian) :
    normalizedSub left right = left - right := by
  rw [normalizedSub, value_sub, value_ofGaussian, value_ofGaussian]

@[simp] theorem normalizedMul_eq (left right : SemanticGaussian) :
    normalizedMul left right = left * right := by
  rw [normalizedMul, value_mul, value_ofGaussian, value_ofGaussian]

@[simp] theorem normalizedInv_eq (source : SemanticGaussian) :
    normalizedInv source = source⁻¹ := by
  rw [normalizedInv, value_inv, value_ofGaussian]

@[simp] theorem normalizedDiv_eq (left right : SemanticGaussian) :
    normalizedDiv left right = left / right := by
  rw [normalizedDiv, value_div, value_ofGaussian, value_ofGaussian]

end RFAP.NormalizedGaussian
