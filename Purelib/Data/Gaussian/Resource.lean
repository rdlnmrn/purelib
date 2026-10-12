module
import Purelib.Data.Nat.Order

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic

public import Purelib.Data.Nat.BitWidth
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Basic
public import Purelib.Data.Rat.Fraction.Resource.Clauses
import Purelib.Data.Rat.Fraction.Resource.Components

import Mathlib.Order.Basic
import Mathlib.Order.MinMax

open Purelib.Data Purelib.Data.Gaussian Purelib.Data.Rat.Fraction.Resource

open Purelib.Data.Rat

section
section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

section
@[expose] public section

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

namespace Purelib.Data.Gaussian.Resource.ClearingCalculationSize

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Take the larger reduced-fraction component magnitude of the two canonical Gaussian coordinates. -/
def coefficientComponentMagnitude (coefficient :
  Basic.Canonical) : Nat :=
  max
    (Fraction.Resource.Components.NormalizedFraction.componentMagnitude
      (Fraction.Basic.ofRational coefficient.re))
    (Fraction.Resource.Components.NormalizedFraction.componentMagnitude
      (Fraction.Basic.ofRational coefficient.im))
end Purelib.Data.Gaussian.Resource.ClearingCalculationSize

end

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource.GaussianNormalized

/-! ## Component envelopes -/

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Take the larger reduced-fraction component magnitude of the two retained normalized Gaussian coordinates. -/
def componentMagnitude (source : Basic.Number) : Nat :=
  max (Fraction.Resource.Components.NormalizedFraction.componentMagnitude source.re)
    (Fraction.Resource.Components.NormalizedFraction.componentMagnitude source.im)
end Purelib.Data.Gaussian.Resource.GaussianNormalized

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Rat in
/-- Compute the Gaussian addition output-magnitude envelope from the supplied component bounds.

Add the two original scalar coordinate costs; the magnitude envelope is the scalar additive envelope on the input
bounds. -/
def addMagnitudeEnvelope (left right : Nat) : Nat :=
  Fraction.Resource.Components.additiveMagnitudeEnvelope left right
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Increasing the supplied component bounds increases the Gaussian addition magnitude envelope. -/
theorem addMagnitudeEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    addMagnitudeEnvelope left right ≤
      addMagnitudeEnvelope leftBound rightBound :=
  Fraction.Resource.Components.additiveMagnitudeEnvelope_mono leftLe rightLe
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Rat in
/-- Compute a scalar-operation cost envelope for Gaussian addition from the supplied component bounds.

Add the two original scalar coordinate costs; the magnitude envelope is the scalar additive envelope on the input
bounds. -/
def addStepEnvelope (left right : Nat) : Nat :=
  Fraction.Resource.Clauses.addStepEnvelope left right +
    Fraction.Resource.Clauses.addStepEnvelope left right
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Increasing the supplied component bounds increases the Gaussian addition step-cost envelope. -/
theorem addStepEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    addStepEnvelope left right ≤ addStepEnvelope leftBound rightBound :=
  Nat.add_le_add
    (Fraction.Resource.Clauses.addStepEnvelope_mono leftLe rightLe)
    (Fraction.Resource.Clauses.addStepEnvelope_mono leftLe rightLe)
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

/-! ## Arithmetic-step envelopes -/

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Compute the retained rational-operation cost of Gaussian addition.

Add the two original scalar coordinate costs; the magnitude envelope is the scalar additive envelope on the input
bounds. -/
def addSteps (left right : Basic.Number) : Nat :=
  Fraction.Resource.Clauses.addSteps left.re right.re +
    Fraction.Resource.Clauses.addSteps left.im right.im
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

/-- The imaginary component magnitude is bounded by the displayed component maximum.

The Gaussian magnitude retains the maximum of the original real and imaginary
component magnitudes, so its second contribution supplies this bound. -/
theorem imaginaryMagnitude_le (source : Basic.Number) :
    Fraction.Resource.Components.NormalizedFraction.componentMagnitude source.im ≤
      Resource.GaussianNormalized.componentMagnitude source :=
  Nat.Order.le_max_right _ _
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Rat in
/-- Compute the Gaussian multiplication output-magnitude envelope from the supplied component bounds.

Retain four coordinate products, then one real-coordinate subtraction and one imaginary-coordinate addition. Bound the
intermediate products with the original scalar multiplicative magnitude envelope. -/
def mulMagnitudeEnvelope (left right : Nat) : Nat :=
  let product :=
    Fraction.Resource.Components.multiplicativeMagnitudeEnvelope left right
  Fraction.Resource.Components.additiveMagnitudeEnvelope product product
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Increasing the supplied component bounds increases the Gaussian multiplication magnitude envelope. -/
theorem mulMagnitudeEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    mulMagnitudeEnvelope left right ≤
      mulMagnitudeEnvelope leftBound rightBound := by
  unfold mulMagnitudeEnvelope
  let product :=
    Fraction.Resource.Components.multiplicativeMagnitudeEnvelope left right
  let productBound :=
    Fraction.Resource.Components.multiplicativeMagnitudeEnvelope
      leftBound rightBound
  have productLe : product ≤ productBound :=
    Fraction.Resource.Components.multiplicativeMagnitudeEnvelope_mono
      leftLe rightLe
  exact Fraction.Resource.Components.additiveMagnitudeEnvelope_mono
    productLe productLe
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Rat in
/-- Compute a scalar-operation cost envelope for Gaussian multiplication from the supplied component bounds.

Retain four coordinate products, then one real-coordinate subtraction and one imaginary-coordinate addition. Bound the
intermediate products with the original scalar multiplicative magnitude envelope. -/
def mulStepEnvelope (left right : Nat) : Nat :=
  let product :=
    Fraction.Resource.Components.multiplicativeMagnitudeEnvelope left right
  Fraction.Resource.Clauses.mulStepEnvelope left right +
    Fraction.Resource.Clauses.mulStepEnvelope left right +
    Fraction.Resource.Clauses.mulStepEnvelope left right +
    Fraction.Resource.Clauses.mulStepEnvelope left right +
    Fraction.Resource.Clauses.subStepEnvelope product product +
    Fraction.Resource.Clauses.addStepEnvelope product product
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Increasing the supplied component bounds increases the Gaussian multiplication step-cost envelope. -/
theorem mulStepEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    mulStepEnvelope left right ≤ mulStepEnvelope leftBound rightBound := by
  let product :=
    Fraction.Resource.Components.multiplicativeMagnitudeEnvelope left right
  let productBound :=
    Fraction.Resource.Components.multiplicativeMagnitudeEnvelope
      leftBound rightBound
  have scalar := Fraction.Resource.Clauses.mulStepEnvelope_mono leftLe rightLe
  have productLe : product ≤ productBound :=
    Fraction.Resource.Components.multiplicativeMagnitudeEnvelope_mono
      leftLe rightLe
  have subtraction := Fraction.Resource.Clauses.subStepEnvelope_mono
    productLe productLe
  have addition := Fraction.Resource.Clauses.addStepEnvelope_mono
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
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Compute the retained rational-operation cost of Gaussian multiplication.

Retain four coordinate products, then one real-coordinate subtraction and one imaginary-coordinate addition. Bound the
intermediate products with the original scalar multiplicative magnitude envelope. -/
def mulSteps (left right : Basic.Number) : Nat :=
  let realLeft := Fraction.Arithmetic.mul left.re right.re
  let realRight := Fraction.Arithmetic.mul left.im right.im
  let imaginaryLeft := Fraction.Arithmetic.mul left.re right.im
  let imaginaryRight := Fraction.Arithmetic.mul left.im right.re
  Fraction.Resource.Clauses.mulSteps left.re right.re +
    Fraction.Resource.Clauses.mulSteps left.im right.im +
    Fraction.Resource.Clauses.mulSteps left.re right.im +
    Fraction.Resource.Clauses.mulSteps left.im right.re +
    Fraction.Resource.Clauses.subSteps realLeft realRight +
    Fraction.Resource.Clauses.addSteps imaginaryLeft imaginaryRight
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Rat in
/-- Compute a scalar-operation cost envelope for Gaussian negation from the supplied component bounds.

Negate both original reduced rational coordinates and add their scalar negation costs. The component magnitude does not
increase. -/
def negStepEnvelope (source : Nat) : Nat :=
  Fraction.Resource.Clauses.negStepEnvelope source +
    Fraction.Resource.Clauses.negStepEnvelope source
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Increasing the supplied component bounds increases the Gaussian negation step-cost envelope. -/
theorem negStepEnvelope_mono {source bound : Nat} (sourceLe : source ≤ bound) :
    negStepEnvelope source ≤ negStepEnvelope bound :=
  Nat.add_le_add
    (Fraction.Resource.Clauses.negStepEnvelope_mono sourceLe)
    (Fraction.Resource.Clauses.negStepEnvelope_mono sourceLe)
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Compute the retained rational-operation cost of Gaussian negation.

Negate both original reduced rational coordinates and add their scalar negation costs. The component magnitude does not
increase. -/
def negSteps (source : Basic.Number) : Nat :=
  Fraction.Resource.Clauses.negSteps source.re +
    Fraction.Resource.Clauses.negSteps source.im
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Rat in
/-- Compute the Gaussian squared norm output-magnitude envelope from the supplied component bounds.

Square each retained coordinate and add the two squares. Intermediate square magnitudes use the scalar multiplicative
envelope at the same input bound. -/
def normSqMagnitudeEnvelope (source : Nat) : Nat :=
  let square :=
    Fraction.Resource.Components.multiplicativeMagnitudeEnvelope source source
  Fraction.Resource.Components.additiveMagnitudeEnvelope square square
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Compute the Gaussian inversion output-magnitude envelope from the supplied component bounds.

Compute the retained norm-square denominator, divide both coordinates by it and negate the imaginary coordinate. The
cost includes that same denominator computation and both scalar divisions, including the totalized zero case. -/
def invMagnitudeEnvelope (source : Nat) : Nat :=
  Fraction.Resource.Components.multiplicativeMagnitudeEnvelope source
    (normSqMagnitudeEnvelope source)
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
/-- Compute the Gaussian division output-magnitude envelope from the supplied component bounds.

Compute the inverse of the retained right input and multiply the original left input by that inverse. The bound feeds
the inverse magnitude envelope into the multiplication envelope. -/
def divMagnitudeEnvelope (left right : Nat) : Nat :=
  mulMagnitudeEnvelope left (invMagnitudeEnvelope right)
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Increasing the supplied component bounds increases the Gaussian squared norm magnitude envelope. -/
theorem normSqMagnitudeEnvelope_mono {source bound : Nat}
    (sourceLe : source ≤ bound) :
    normSqMagnitudeEnvelope source ≤ normSqMagnitudeEnvelope bound := by
  unfold normSqMagnitudeEnvelope
  have squareLe := Fraction.Resource.Components.multiplicativeMagnitudeEnvelope_mono
    sourceLe sourceLe
  exact Fraction.Resource.Components.additiveMagnitudeEnvelope_mono
    squareLe squareLe
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Increasing the supplied component bounds increases the Gaussian inversion magnitude envelope. -/
theorem invMagnitudeEnvelope_mono {source bound : Nat}
    (sourceLe : source ≤ bound) :
    invMagnitudeEnvelope source ≤ invMagnitudeEnvelope bound := by
  unfold invMagnitudeEnvelope
  exact Fraction.Resource.Components.multiplicativeMagnitudeEnvelope_mono
    sourceLe (normSqMagnitudeEnvelope_mono sourceLe)
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
/-- Increasing the supplied component bounds increases the Gaussian division magnitude envelope. -/
theorem divMagnitudeEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    divMagnitudeEnvelope left right ≤
      divMagnitudeEnvelope leftBound rightBound := by
  unfold divMagnitudeEnvelope
  exact mulMagnitudeEnvelope_mono leftLe (invMagnitudeEnvelope_mono rightLe)
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Rat in
/-- Compute a scalar-operation cost envelope for Gaussian squared norm from the supplied component bounds.

Square each retained coordinate and add the two squares. Intermediate square magnitudes use the scalar multiplicative
envelope at the same input bound. -/
def normSqStepEnvelope (source : Nat) : Nat :=
  let square :=
    Fraction.Resource.Components.multiplicativeMagnitudeEnvelope source source
  Fraction.Resource.Clauses.mulStepEnvelope source source +
    Fraction.Resource.Clauses.mulStepEnvelope source source +
    Fraction.Resource.Clauses.addStepEnvelope square square
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Compute a scalar-operation cost envelope for Gaussian inversion from the supplied component bounds.

Compute the retained norm-square denominator, divide both coordinates by it and negate the imaginary coordinate. The
cost includes that same denominator computation and both scalar divisions, including the totalized zero case. -/
def invStepEnvelope (source : Nat) : Nat :=
  let normBound := normSqMagnitudeEnvelope source
  normSqStepEnvelope source +
    Fraction.Resource.Clauses.divStepEnvelope source normBound +
    Fraction.Resource.Clauses.negStepEnvelope source +
    Fraction.Resource.Clauses.divStepEnvelope source normBound
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
/-- Compute a scalar-operation cost envelope for Gaussian division from the supplied component bounds.

Compute the inverse of the retained right input and multiply the original left input by that inverse. The bound feeds
the inverse magnitude envelope into the multiplication envelope. -/
def divStepEnvelope (left right : Nat) : Nat :=
  invStepEnvelope right + mulStepEnvelope left (invMagnitudeEnvelope right)
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Increasing the supplied component bounds increases the Gaussian squared norm step-cost envelope. -/
theorem normSqStepEnvelope_mono {source bound : Nat}
    (sourceLe : source ≤ bound) :
    normSqStepEnvelope source ≤ normSqStepEnvelope bound := by
  let square :=
    Fraction.Resource.Components.multiplicativeMagnitudeEnvelope source source
  let squareBound :=
    Fraction.Resource.Components.multiplicativeMagnitudeEnvelope bound bound
  have multiplication := Fraction.Resource.Clauses.mulStepEnvelope_mono
    sourceLe sourceLe
  have squareLe : square ≤ squareBound :=
    Fraction.Resource.Components.multiplicativeMagnitudeEnvelope_mono
      sourceLe sourceLe
  have addition := Fraction.Resource.Clauses.addStepEnvelope_mono
    squareLe squareLe
  unfold normSqStepEnvelope
  dsimp only [square, squareBound] at multiplication addition ⊢
  exact Nat.add_le_add
    (Nat.add_le_add multiplication multiplication)
    addition
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Increasing the supplied component bounds increases the Gaussian inversion step-cost envelope. -/
theorem invStepEnvelope_mono {source bound : Nat} (sourceLe : source ≤ bound) :
    invStepEnvelope source ≤ invStepEnvelope bound := by
  let normBound := normSqMagnitudeEnvelope source
  let largerNormBound := normSqMagnitudeEnvelope bound
  have normLe : normBound ≤ largerNormBound :=
    normSqMagnitudeEnvelope_mono sourceLe
  have normSteps := normSqStepEnvelope_mono sourceLe
  have division := Fraction.Resource.Clauses.divStepEnvelope_mono
    sourceLe normLe
  have negation := Fraction.Resource.Clauses.negStepEnvelope_mono sourceLe
  unfold invStepEnvelope
  dsimp only [normBound, largerNormBound] at normSteps division negation ⊢
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add normSteps division)
      negation)
    division
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
/-- Increasing the supplied component bounds increases the Gaussian division step-cost envelope. -/
theorem divStepEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    divStepEnvelope left right ≤ divStepEnvelope leftBound rightBound := by
  unfold divStepEnvelope
  exact Nat.add_le_add (invStepEnvelope_mono rightLe)
    (mulStepEnvelope_mono leftLe (invMagnitudeEnvelope_mono rightLe))
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Compute the retained rational-operation cost of Gaussian squared norm.

Square each retained coordinate and add the two squares. Intermediate square magnitudes use the scalar multiplicative
envelope at the same input bound. -/
def normSqSteps (source : Basic.Number) : Nat :=
  let realSquare := Fraction.Arithmetic.mul source.re source.re
  let imaginarySquare := Fraction.Arithmetic.mul source.im source.im
  Fraction.Resource.Clauses.mulSteps source.re source.re +
    Fraction.Resource.Clauses.mulSteps source.im source.im +
    Fraction.Resource.Clauses.addSteps realSquare imaginarySquare
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Compute the retained rational-operation cost of Gaussian inversion.

Compute the retained norm-square denominator, divide both coordinates by it and negate the imaginary coordinate. The
cost includes that same denominator computation and both scalar divisions, including the totalized zero case. -/
def invSteps (source : Basic.Number) : Nat :=
  let denominator := Norm.Basic.GaussianNormalized.normSq source
  normSqSteps source +
    Fraction.Resource.Clauses.divSteps source.re denominator +
    Fraction.Resource.Clauses.negSteps source.im +
    Fraction.Resource.Clauses.divSteps
      (Fraction.Arithmetic.neg source.im) denominator
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
/-- Compute the retained rational-operation cost of Gaussian division.

Compute the inverse of the retained right input and multiply the original left input by that inverse. The bound feeds
the inverse magnitude envelope into the multiplication envelope. -/
def divSteps (left right : Basic.Number) : Nat :=
  invSteps right + mulSteps left (Field.GaussianNormalized.inv right)
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

/-- The real component magnitude is bounded by the displayed component maximum.

The Gaussian magnitude retains the maximum of the original real and imaginary
component magnitudes, so its first contribution supplies this bound. -/
theorem realMagnitude_le (source : Basic.Number) :
    Fraction.Resource.Components.NormalizedFraction.componentMagnitude source.re ≤
      Resource.GaussianNormalized.componentMagnitude source :=
  Nat.Order.le_max_left _ _
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained Gaussian addition cost is bounded by its step envelope evaluated at the original input component
magnitudes. -/
theorem addSteps_le_envelope (left right : Basic.Number) :
    addSteps left right ≤
      addStepEnvelope (Resource.GaussianNormalized.componentMagnitude left)
        (Resource.GaussianNormalized.componentMagnitude right) := by
  unfold addSteps addStepEnvelope
  exact Nat.add_le_add
    ((Fraction.Resource.Clauses.addSteps_le_envelope left.re right.re).trans
      (Fraction.Resource.Clauses.addStepEnvelope_mono
        (realMagnitude_le left) (realMagnitude_le right)))
    ((Fraction.Resource.Clauses.addSteps_le_envelope left.im right.im).trans
      (Fraction.Resource.Clauses.addStepEnvelope_mono
        (imaginaryMagnitude_le left) (imaginaryMagnitude_le right)))
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

/-- The displayed sum magnitude is bounded by the two-input addition envelope.

Both retained rational coordinate sums satisfy the same envelope after
transporting their original magnitudes into the Gaussian component maxima. -/
theorem componentMagnitude_add_le (left right : Basic.Number) :
    Resource.GaussianNormalized.componentMagnitude (Basic.add left right) ≤
      addMagnitudeEnvelope (Resource.GaussianNormalized.componentMagnitude left)
        (Resource.GaussianNormalized.componentMagnitude right) := by
  apply Nat.Order.max_le
  · exact (Components.componentMagnitude_add_le_magnitudeEnvelope
      left.re right.re).trans
        (Components.additiveMagnitudeEnvelope_mono
          (realMagnitude_le left) (realMagnitude_le right))
  · exact (Components.componentMagnitude_add_le_magnitudeEnvelope
      left.im right.im).trans
        (Components.additiveMagnitudeEnvelope_mono
          (imaginaryMagnitude_le left) (imaginaryMagnitude_le right))
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

/-- The displayed product magnitude is bounded by the two-input multiplication envelope.

The four retained coordinate products are bounded before their difference
and sum are formed, preserving the original product and addition envelopes. -/
theorem componentMagnitude_mul_le (left right : Basic.Number) :
    Resource.GaussianNormalized.componentMagnitude (Basic.mul left right) ≤
      mulMagnitudeEnvelope (Resource.GaussianNormalized.componentMagnitude left)
        (Resource.GaussianNormalized.componentMagnitude right) := by
  let product := Components.multiplicativeMagnitudeEnvelope
    (Resource.GaussianNormalized.componentMagnitude left) (Resource.GaussianNormalized.componentMagnitude right)
  have realLeft : Components.NormalizedFraction.componentMagnitude
      (Rat.Fraction.Arithmetic.mul left.re right.re) ≤ product :=
    (Components.componentMagnitude_mul_le_magnitudeEnvelope left.re right.re).trans
      (Components.multiplicativeMagnitudeEnvelope_mono
        (realMagnitude_le left) (realMagnitude_le right))
  have realRight : Components.NormalizedFraction.componentMagnitude
      (Rat.Fraction.Arithmetic.mul left.im right.im) ≤ product :=
    (Components.componentMagnitude_mul_le_magnitudeEnvelope left.im right.im).trans
      (Components.multiplicativeMagnitudeEnvelope_mono
        (imaginaryMagnitude_le left) (imaginaryMagnitude_le right))
  have imaginaryLeft : Components.NormalizedFraction.componentMagnitude
      (Rat.Fraction.Arithmetic.mul left.re right.im) ≤ product :=
    (Components.componentMagnitude_mul_le_magnitudeEnvelope left.re right.im).trans
      (Components.multiplicativeMagnitudeEnvelope_mono
        (realMagnitude_le left) (imaginaryMagnitude_le right))
  have imaginaryRight : Components.NormalizedFraction.componentMagnitude
      (Rat.Fraction.Arithmetic.mul left.im right.re) ≤ product :=
    (Components.componentMagnitude_mul_le_magnitudeEnvelope left.im right.re).trans
      (Components.multiplicativeMagnitudeEnvelope_mono
        (imaginaryMagnitude_le left) (realMagnitude_le right))
  apply Nat.Order.max_le
  · exact (Components.componentMagnitude_sub_le _ _).trans
      (Components.additiveMagnitudeEnvelope_mono
        realLeft realRight)
  · exact (Components.componentMagnitude_add_le_magnitudeEnvelope _ _).trans
      (Components.additiveMagnitudeEnvelope_mono
        imaginaryLeft imaginaryRight)
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

/-- Negating a Gaussian rational does not increase its component magnitude.

Each retained coordinate negation is bounded by its original magnitude,
which is a contribution to the unchanged Gaussian component maximum. -/
theorem componentMagnitude_neg_le (source : Basic.Number) :
    Resource.GaussianNormalized.componentMagnitude (Basic.neg source) ≤ Resource.GaussianNormalized.componentMagnitude
      source := by
  apply Nat.Order.max_le
  · exact (Components.componentMagnitude_neg_le source.re).trans
      (realMagnitude_le source)
  · exact (Components.componentMagnitude_neg_le source.im).trans
      (imaginaryMagnitude_le source)
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The component magnitude after Gaussian squared norm is bounded by the corresponding envelope at the original input
component magnitudes. -/
theorem componentMagnitude_normSq_le (source : Basic.Number) :
    Fraction.Resource.Components.NormalizedFraction.componentMagnitude (Norm.Basic.GaussianNormalized.normSq source) ≤
      normSqMagnitudeEnvelope (Resource.GaussianNormalized.componentMagnitude source) := by
  let square := Fraction.Resource.Components.multiplicativeMagnitudeEnvelope
    (Resource.GaussianNormalized.componentMagnitude source) (Resource.GaussianNormalized.componentMagnitude source)
  have realSquare : Fraction.Resource.Components.NormalizedFraction.componentMagnitude
      (Fraction.Arithmetic.mul source.re source.re) ≤ square :=
    (Fraction.Resource.Components.componentMagnitude_mul_le_magnitudeEnvelope source.re source.re).trans
      (Fraction.Resource.Components.multiplicativeMagnitudeEnvelope_mono
        (realMagnitude_le source) (realMagnitude_le source))
  have imaginarySquare : Fraction.Resource.Components.NormalizedFraction.componentMagnitude
      (Fraction.Arithmetic.mul source.im source.im) ≤ square :=
    (Fraction.Resource.Components.componentMagnitude_mul_le_magnitudeEnvelope source.im source.im).trans
      (Fraction.Resource.Components.multiplicativeMagnitudeEnvelope_mono
        (imaginaryMagnitude_le source) (imaginaryMagnitude_le source))
  exact (Fraction.Resource.Components.componentMagnitude_add_le_magnitudeEnvelope _ _).trans
    (Fraction.Resource.Components.additiveMagnitudeEnvelope_mono
      realSquare imaginarySquare)
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

/-- The displayed inverse magnitude is bounded by the original inverse envelope.

The retained squared norm bounds the denominator of both coordinate
divisions; the imaginary coordinate also retains its negation bound. -/
theorem componentMagnitude_inv_le (source : Basic.Number) :
    Resource.GaussianNormalized.componentMagnitude (Field.GaussianNormalized.inv source) ≤
      invMagnitudeEnvelope (Resource.GaussianNormalized.componentMagnitude source) := by
  have denominatorBound := componentMagnitude_normSq_le source
  apply Nat.Order.max_le
  · exact (Components.componentMagnitude_div_le _ _).trans
      (Components.multiplicativeMagnitudeEnvelope_mono
        (realMagnitude_le source) denominatorBound)
  · exact (Components.componentMagnitude_div_le _ _).trans
      (Components.multiplicativeMagnitudeEnvelope_mono
        ((Components.componentMagnitude_neg_le source.im).trans
          (imaginaryMagnitude_le source)) denominatorBound)
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The component magnitude after Gaussian division is bounded by the corresponding envelope at the original input
component magnitudes. -/
theorem componentMagnitude_div_le (left right : Basic.Number) :
    Resource.GaussianNormalized.componentMagnitude (Field.div left right) ≤
      divMagnitudeEnvelope (Resource.GaussianNormalized.componentMagnitude left)
        (Resource.GaussianNormalized.componentMagnitude right) := by
  exact (componentMagnitude_mul_le left (Field.GaussianNormalized.inv right)).trans
    (by
      unfold divMagnitudeEnvelope
      let leftMagnitude := Resource.GaussianNormalized.componentMagnitude left
      let inverseMagnitude := Resource.GaussianNormalized.componentMagnitude (Field.GaussianNormalized.inv right)
      let inverseBound := invMagnitudeEnvelope (Resource.GaussianNormalized.componentMagnitude right)
      let product := Fraction.Resource.Components.multiplicativeMagnitudeEnvelope
        leftMagnitude inverseMagnitude
      let productBound := Fraction.Resource.Components.multiplicativeMagnitudeEnvelope
        leftMagnitude inverseBound
      apply Fraction.Resource.Components.additiveMagnitudeEnvelope_mono
      · exact Fraction.Resource.Components.multiplicativeMagnitudeEnvelope_mono
          (le_refl _) (componentMagnitude_inv_le right)
      · exact Fraction.Resource.Components.multiplicativeMagnitudeEnvelope_mono
          (le_refl _) (componentMagnitude_inv_le right))
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The component magnitude after Gaussian subtraction is bounded by the corresponding envelope at the original input
component magnitudes. -/
theorem componentMagnitude_sub_le (left right : Basic.Number) :
    Resource.GaussianNormalized.componentMagnitude (Basic.sub left right) ≤
      addMagnitudeEnvelope (Resource.GaussianNormalized.componentMagnitude left)
        (Resource.GaussianNormalized.componentMagnitude right) := by
  exact (componentMagnitude_add_le left (Basic.neg right)).trans
    (Fraction.Resource.Components.additiveMagnitudeEnvelope_mono (le_refl _)
      (componentMagnitude_neg_le right))
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained Gaussian multiplication cost is bounded by its step envelope evaluated at the original input component
magnitudes. -/
theorem mulSteps_le_envelope (left right : Basic.Number) :
    mulSteps left right ≤
      mulStepEnvelope (Resource.GaussianNormalized.componentMagnitude left)
        (Resource.GaussianNormalized.componentMagnitude right) := by
  let product := Fraction.Resource.Components.multiplicativeMagnitudeEnvelope
    (Resource.GaussianNormalized.componentMagnitude left) (Resource.GaussianNormalized.componentMagnitude right)
  let realLeft := Fraction.Arithmetic.mul left.re right.re
  let realRight := Fraction.Arithmetic.mul left.im right.im
  let imaginaryLeft := Fraction.Arithmetic.mul left.re right.im
  let imaginaryRight := Fraction.Arithmetic.mul left.im right.re
  have realLeftMagnitude : Fraction.Resource.Components.NormalizedFraction.componentMagnitude
      realLeft ≤ product :=
    (Fraction.Resource.Components.componentMagnitude_mul_le_magnitudeEnvelope left.re right.re).trans
      (Fraction.Resource.Components.multiplicativeMagnitudeEnvelope_mono
        (realMagnitude_le left) (realMagnitude_le right))
  have realRightMagnitude : Fraction.Resource.Components.NormalizedFraction.componentMagnitude
      realRight ≤ product :=
    (Fraction.Resource.Components.componentMagnitude_mul_le_magnitudeEnvelope left.im right.im).trans
      (Fraction.Resource.Components.multiplicativeMagnitudeEnvelope_mono
        (imaginaryMagnitude_le left) (imaginaryMagnitude_le right))
  have imaginaryLeftMagnitude : Fraction.Resource.Components.NormalizedFraction.componentMagnitude
      imaginaryLeft ≤ product :=
    (Fraction.Resource.Components.componentMagnitude_mul_le_magnitudeEnvelope left.re right.im).trans
      (Fraction.Resource.Components.multiplicativeMagnitudeEnvelope_mono
        (realMagnitude_le left) (imaginaryMagnitude_le right))
  have imaginaryRightMagnitude : Fraction.Resource.Components.NormalizedFraction.componentMagnitude
      imaginaryRight ≤ product :=
    (Fraction.Resource.Components.componentMagnitude_mul_le_magnitudeEnvelope left.im right.re).trans
      (Fraction.Resource.Components.multiplicativeMagnitudeEnvelope_mono
        (imaginaryMagnitude_le left) (realMagnitude_le right))
  have first := (Fraction.Resource.Clauses.mulSteps_le_envelope
    left.re right.re).trans
      (Fraction.Resource.Clauses.mulStepEnvelope_mono
        (realMagnitude_le left) (realMagnitude_le right))
  have second := (Fraction.Resource.Clauses.mulSteps_le_envelope
    left.im right.im).trans
      (Fraction.Resource.Clauses.mulStepEnvelope_mono
        (imaginaryMagnitude_le left) (imaginaryMagnitude_le right))
  have third := (Fraction.Resource.Clauses.mulSteps_le_envelope
    left.re right.im).trans
      (Fraction.Resource.Clauses.mulStepEnvelope_mono
        (realMagnitude_le left) (imaginaryMagnitude_le right))
  have fourth := (Fraction.Resource.Clauses.mulSteps_le_envelope
    left.im right.re).trans
      (Fraction.Resource.Clauses.mulStepEnvelope_mono
        (imaginaryMagnitude_le left) (realMagnitude_le right))
  have fifth := (Fraction.Resource.Clauses.subSteps_le_envelope
    realLeft realRight).trans
      (Fraction.Resource.Clauses.subStepEnvelope_mono
        realLeftMagnitude realRightMagnitude)
  have sixth := (Fraction.Resource.Clauses.addSteps_le_envelope
    imaginaryLeft imaginaryRight).trans
      (Fraction.Resource.Clauses.addStepEnvelope_mono
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
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained Gaussian negation cost is bounded by its step envelope evaluated at the original input component
magnitudes. -/
theorem negSteps_le_envelope (source : Basic.Number) :
    negSteps source ≤ negStepEnvelope (Resource.GaussianNormalized.componentMagnitude source) := by
  unfold negSteps negStepEnvelope
  exact Nat.add_le_add
    ((Fraction.Resource.Clauses.negSteps_le_envelope source.re).trans
      (Fraction.Resource.Clauses.negStepEnvelope_mono
        (realMagnitude_le source)))
    ((Fraction.Resource.Clauses.negSteps_le_envelope source.im).trans
      (Fraction.Resource.Clauses.negStepEnvelope_mono
        (imaginaryMagnitude_le source)))
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained Gaussian squared norm cost is bounded by its step envelope evaluated at the original input component
magnitudes. -/
theorem normSqSteps_le_envelope (source : Basic.Number) :
    normSqSteps source ≤ normSqStepEnvelope (Resource.GaussianNormalized.componentMagnitude source) :=
      by
  let square := Fraction.Resource.Components.multiplicativeMagnitudeEnvelope
    (Resource.GaussianNormalized.componentMagnitude source) (Resource.GaussianNormalized.componentMagnitude source)
  let realSquare := Fraction.Arithmetic.mul source.re source.re
  let imaginarySquare := Fraction.Arithmetic.mul source.im source.im
  have realMagnitude : Fraction.Resource.Components.NormalizedFraction.componentMagnitude
      realSquare ≤ square :=
    (Fraction.Resource.Components.componentMagnitude_mul_le_magnitudeEnvelope source.re source.re).trans
      (Fraction.Resource.Components.multiplicativeMagnitudeEnvelope_mono
        (realMagnitude_le source) (realMagnitude_le source))
  have imaginaryMagnitude : Fraction.Resource.Components.NormalizedFraction.componentMagnitude
      imaginarySquare ≤ square :=
    (Fraction.Resource.Components.componentMagnitude_mul_le_magnitudeEnvelope source.im source.im).trans
      (Fraction.Resource.Components.multiplicativeMagnitudeEnvelope_mono
        (imaginaryMagnitude_le source) (imaginaryMagnitude_le source))
  have first := (Fraction.Resource.Clauses.mulSteps_le_envelope
    source.re source.re).trans
      (Fraction.Resource.Clauses.mulStepEnvelope_mono
        (realMagnitude_le source) (realMagnitude_le source))
  have second := (Fraction.Resource.Clauses.mulSteps_le_envelope
    source.im source.im).trans
      (Fraction.Resource.Clauses.mulStepEnvelope_mono
        (imaginaryMagnitude_le source) (imaginaryMagnitude_le source))
  have third := (Fraction.Resource.Clauses.addSteps_le_envelope
    realSquare imaginarySquare).trans
      (Fraction.Resource.Clauses.addStepEnvelope_mono
        realMagnitude imaginaryMagnitude)
  unfold normSqSteps normSqStepEnvelope
  dsimp only [realSquare, imaginarySquare, square]
    at first second third ⊢
  exact Nat.add_le_add (Nat.add_le_add first second) third
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained Gaussian inversion cost is bounded by its step envelope evaluated at the original input component
magnitudes. -/
theorem invSteps_le_envelope (source : Basic.Number) :
    invSteps source ≤ invStepEnvelope (Resource.GaussianNormalized.componentMagnitude source) := by
  let denominator := Norm.Basic.GaussianNormalized.normSq source
  let normBound := normSqMagnitudeEnvelope (Resource.GaussianNormalized.componentMagnitude source)
  have denominatorMagnitude : Fraction.Resource.Components.NormalizedFraction.componentMagnitude
      denominator ≤ normBound := componentMagnitude_normSq_le source
  have normStepsBound := normSqSteps_le_envelope source
  have realDivision := (Fraction.Resource.Clauses.divSteps_le_envelope
    source.re denominator).trans
      (Fraction.Resource.Clauses.divStepEnvelope_mono
        (realMagnitude_le source) denominatorMagnitude)
  have negation := (Fraction.Resource.Clauses.negSteps_le_envelope
    source.im).trans
      (Fraction.Resource.Clauses.negStepEnvelope_mono
        (imaginaryMagnitude_le source))
  have imaginaryDivision := (Fraction.Resource.Clauses.divSteps_le_envelope
    (Fraction.Arithmetic.neg source.im) denominator).trans
      (Fraction.Resource.Clauses.divStepEnvelope_mono
        ((Fraction.Resource.Components.componentMagnitude_neg_le source.im).trans
          (imaginaryMagnitude_le source)) denominatorMagnitude)
  have combined := Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add normStepsBound realDivision) negation)
    imaginaryDivision
  simpa only [invSteps, invStepEnvelope, denominator, normBound] using combined
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
/-- The retained Gaussian division cost is bounded by its step envelope evaluated at the original input component
magnitudes. -/
theorem divSteps_le_envelope (left right : Basic.Number) :
    divSteps left right ≤
      divStepEnvelope (Resource.GaussianNormalized.componentMagnitude left)
        (Resource.GaussianNormalized.componentMagnitude right) := by
  have inverseSteps := invSteps_le_envelope right
  have multiplication := (mulSteps_le_envelope left (Field.GaussianNormalized.inv right)).trans
    (mulStepEnvelope_mono
      (left := Resource.GaussianNormalized.componentMagnitude left)
      (right := Resource.GaussianNormalized.componentMagnitude (Field.GaussianNormalized.inv right))
      (leftBound := Resource.GaussianNormalized.componentMagnitude left)
      (rightBound := invMagnitudeEnvelope (Resource.GaussianNormalized.componentMagnitude right))
      (le_refl _) (componentMagnitude_inv_le right))
  unfold divSteps divStepEnvelope
  exact Nat.add_le_add inverseSteps multiplication
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
/-- Compute a scalar-operation cost envelope for Gaussian subtraction from the supplied component bounds.

Negate the retained right input and add it to the original left input. The envelope keeps both input magnitudes and the
separate negation and addition costs. -/
def subStepEnvelope (left right : Nat) : Nat :=
  negStepEnvelope right + addStepEnvelope left right
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
/-- Increasing the supplied component bounds increases the Gaussian subtraction step-cost envelope. -/
theorem subStepEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    subStepEnvelope left right ≤ subStepEnvelope leftBound rightBound := by
  unfold subStepEnvelope
  exact Nat.add_le_add (negStepEnvelope_mono rightLe)
    (addStepEnvelope_mono leftLe rightLe)
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
/-- Compute the retained rational-operation cost of Gaussian subtraction.

Negate the retained right input and add it to the original left input. The envelope keeps both input magnitudes and the
separate negation and addition costs. -/
def subSteps (left right : Basic.Number) : Nat :=
  negSteps right + addSteps left (Basic.neg right)
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
section
@[expose] public section

/-!
# Normalized Gaussian-rational working arithmetic

Gaussian computations use two canonical rational-coordinate records.  The
working and semantic carriers now coincide structurally; this module retains
the published normalized-operation and calculation-size API.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
/-- The retained Gaussian subtraction cost is bounded by its step envelope evaluated at the original input component
magnitudes. -/
theorem subSteps_le_envelope (left right : Basic.Number) :
    subSteps left right ≤
      subStepEnvelope (Resource.GaussianNormalized.componentMagnitude left)
        (Resource.GaussianNormalized.componentMagnitude right) := by
  have negBound := negSteps_le_envelope right
  have addBound := addSteps_le_envelope left (Basic.neg right)
  have addEnvelopeBound := addStepEnvelope_mono
    (left := Resource.GaussianNormalized.componentMagnitude left)
    (right := Resource.GaussianNormalized.componentMagnitude (Basic.neg right))
    (leftBound := Resource.GaussianNormalized.componentMagnitude left)
    (rightBound := Resource.GaussianNormalized.componentMagnitude right)
    (le_refl _) (componentMagnitude_neg_le right)
  unfold subSteps subStepEnvelope
  exact Nat.add_le_add negBound (addBound.trans addEnvelopeBound)
end Purelib.Data.Gaussian.Resource

end

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
open Purelib.Data.Nat in
/-- Compute natural bit width of the maximum reduced-coordinate component magnitude. -/
def workingGaussianWidth (value : Basic.Number) : Nat :=
  BitWidth.natWidth (Resource.GaussianNormalized.componentMagnitude value)
end Purelib.Data.Gaussian.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Gaussian.Resource

open Purelib.Data.Gaussian in
/-- Compute normalized component-magnitude bit width of the canonical Gaussian readback. -/
def gaussianRecordWidth (value : Basic.Canonical) : Nat :=
  workingGaussianWidth (Basic.ofGaussian value)
end Purelib.Data.Gaussian.Resource

end

section
@[expose] public section

/-!
# Traced normalized Gaussian-polynomial evaluation

This module runs dense Horner evaluation entirely through reduced Gaussian
rational working records.  Its trace lists every accumulator, its arithmetic
count is computed alongside the same recursion, and source-only recurrences
bound both the count and every intermediate component.  Erasing the final
working record gives the existing dense-polynomial evaluation exactly.
-/

namespace Purelib.Data.Gaussian.Resource

/-! ## Source-only magnitude and Purelib.Polynomial.Dense.Evaluation.step recurrences -/

open Purelib.Data.Gaussian in
/-- Compute the retained Gaussian component magnitude after conversion to the original normalized representation. -/
def componentMagnitude (source : Basic.Canonical) : Nat :=
  Resource.GaussianNormalized.componentMagnitude
    (Basic.ofGaussian source)
end Purelib.Data.Gaussian.Resource

end
