module

public import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Data.Gaussian.Certificate.Raw
import Purelib.Data.Rat.Certificate.Raw
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Gaussian.Certificate

open Purelib.Data.Rat.Certificate

open Purelib.Data.Rat.Certificate.Raw

open Purelib.Geometry

section
@[expose] public section

/-!
# Kernel verifier for generated quartic period data

The companion Python program performs only search and exact integer
arithmetic.  This module is the trust boundary: generated certificates store
displayed integer numerators and positive natural denominators, and the Lean
kernel checks the resulting cross-products before any fact is promoted to a
statement about constructive rationals.

Keeping the unreduced displayed fractions as data is deliberate.  It avoids
asking the elaborator to normalize a large expression in the canonical
rational implementation merely to check an inequality.
-/

section

namespace Purelib.Geometry.Rational.Box.Certificate

set_option genInjectivity false in
/-- Exact rational box data, including its two finite ordering checks.

The four displayed endpoint fractions retain their original rational-data
owners. The two supplied comparison certificates order those same endpoints
before their interpretation as a rational box. -/
structure RationalBoxData where
  /-- The displayed rational lower real-coordinate endpoint. -/ xLower : Raw.RationalData
  /-- The displayed rational upper real-coordinate endpoint. -/ xUpper : Raw.RationalData
  /-- The displayed rational lower imaginary-coordinate endpoint. -/ yLower : Raw.RationalData
  /-- The displayed rational upper imaginary-coordinate endpoint. -/ yUpper : Raw.RationalData
  /-- The exact rational-data check ordering the real endpoints. -/ xValid : RationalData.Le xLower xUpper
  /-- The exact rational-data check ordering the imaginary endpoints. -/ yValid : RationalData.Le yLower yUpper

constructive_injectivity RationalBoxData

end Purelib.Geometry.Rational.Box.Certificate

section

namespace Purelib.Geometry.Rational.Box.Certificate.RationalBoxData

/-- Interpret the displayed rational endpoint data as a box, transporting its two order certificates. -/
def toBox (box :
  RationalBoxData) : Rational.Box where
  xLower := box.xLower.toRational
  xUpper := box.xUpper.toRational
  yLower := box.yLower.toRational
  yUpper := box.yUpper.toRational
  x_valid := RationalData.le_sound box.xValid
  y_valid := RationalData.le_sound box.yValid

/-- Four exact rational-data comparisons certify that a displayed Gaussian point lies in the box. -/
def Contains (box :
  RationalBoxData) (point : Raw.GaussianData) : Prop :=
  RationalData.Le box.xLower point.re ∧
    RationalData.Le point.re box.xUpper ∧
    RationalData.Le box.yLower point.im ∧
    RationalData.Le point.im box.yUpper

/-- Coordinatewise inclusion of one displayed rational box in another. -/
def Refines (inner outer :
  RationalBoxData) : Prop :=
  RationalData.Le outer.xLower inner.xLower ∧
    RationalData.Le inner.xUpper outer.xUpper ∧
    RationalData.Le outer.yLower inner.yLower ∧
    RationalData.Le inner.yUpper outer.yUpper

end Purelib.Geometry.Rational.Box.Certificate.RationalBoxData

namespace Purelib.Riemann.Periods.QuarticPeriodCertificateVerifier.RationalBoxData

/-- Decide raw box membership by the four retained rational comparisons. -/
instance (box : Purelib.Geometry.Rational.Box.Certificate.RationalBoxData) (point : Raw.GaussianData) :
    Decidable (box.Contains point) :=
  inferInstanceAs (Decidable
    (RationalData.Le box.xLower point.re ∧
      RationalData.Le point.re box.xUpper ∧
      RationalData.Le box.yLower point.im ∧
      RationalData.Le point.im box.yUpper))

/-- Decide raw box refinement by the four retained rational comparisons. -/
instance (inner outer : Purelib.Geometry.Rational.Box.Certificate.RationalBoxData) : Decidable (inner.Refines outer) :=
  inferInstanceAs (Decidable
    (RationalData.Le outer.xLower inner.xLower ∧
      RationalData.Le inner.xUpper outer.xUpper ∧
      RationalData.Le outer.yLower inner.yLower ∧
      RationalData.Le inner.yUpper outer.yUpper))

end Purelib.Riemann.Periods.QuarticPeriodCertificateVerifier.RationalBoxData

namespace Purelib.Geometry.Rational.Box.Certificate.RationalBoxData

/-- Checked membership of raw rational data implies membership of the interpreted Gaussian point. -/
theorem contains_sound {box :
  RationalBoxData} {point : Raw.GaussianData}
    (checked : box.Contains point) :
    box.toBox.Contains point.toGaussian :=
  ⟨RationalData.le_sound checked.1,
    RationalData.le_sound checked.2.1,
    RationalData.le_sound checked.2.2.1,
    RationalData.le_sound checked.2.2.2⟩

/-- Checked coordinatewise refinement of raw box data implies refinement of the interpreted boxes. -/
theorem refines_sound {inner outer :
  RationalBoxData}
    (checked : inner.Refines outer) : inner.toBox.Refines outer.toBox :=
  ⟨RationalData.le_sound checked.1,
    RationalData.le_sound checked.2.1,
    RationalData.le_sound checked.2.2.1,
    RationalData.le_sound checked.2.2.2⟩

end Purelib.Geometry.Rational.Box.Certificate.RationalBoxData

end

end

end

end
