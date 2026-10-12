module

public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Rational boxes over constructive coordinates

These boxes contain only four constructive rational endpoints and finite order
certificates.  The norm bound uses endpoint squares directly, avoiding an
absolute-value compatibility layer.
-/

namespace Purelib.Geometry.Rational

set_option genInjectivity false in
/-- An axis-aligned box with ordered constructive-rational endpoints.

The four original rational endpoints determine its closed coordinate
intervals. The two supplied order certificates retain the original
endpoints as their indices without becoming executable comparison data. -/
structure Box where
  /-- The lower real-coordinate endpoint. -/ xLower : Fraction.Rational
  /-- The upper real-coordinate endpoint. -/ xUpper : Fraction.Rational
  /-- The lower imaginary-coordinate endpoint. -/ yLower : Fraction.Rational
  /-- The upper imaginary-coordinate endpoint. -/ yUpper : Fraction.Rational
  /-- The real-coordinate endpoints are ordered. -/ x_valid : xLower ≤ xUpper
  /-- The imaginary-coordinate endpoints are ordered. -/ y_valid : yLower ≤ yUpper

constructive_injectivity Box

namespace Box

/-- Both coordinate intervals of the box have strictly positive length. -/
def Proper (B : Box) : Prop :=
  B.xLower < B.xUpper ∧ B.yLower < B.yUpper

/-- Both coordinates lie in the corresponding closed box intervals. -/
def Contains (B : Box) (z :
  Data.Gaussian.Basic.Canonical) : Prop :=
  B.xLower ≤ z.re ∧ z.re ≤ B.xUpper ∧
    B.yLower ≤ z.im ∧ z.im ≤ B.yUpper

/-- Decide box membership by comparing its four rational endpoints. -/
instance containsDecidable (B :
  Box) (z : Data.Gaussian.Basic.Canonical) :
    Decidable (B.Contains z) := by
  unfold Contains
  infer_instance

/-- Both coordinates lie strictly between the corresponding box endpoints. -/
def StrictContains (B : Box) (z :
  Data.Gaussian.Basic.Canonical) : Prop :=
  B.xLower < z.re ∧ z.re < B.xUpper ∧
    B.yLower < z.im ∧ z.im < B.yUpper

/-- Strict box membership implies closed box membership. -/
theorem StrictContains.contains {B :
  Box} {z : Data.Gaussian.Basic.Canonical}
    (strict : B.StrictContains z) : B.Contains z :=
  ⟨strict.1.le, strict.2.1.le, strict.2.2.1.le, strict.2.2.2.le⟩
end Box

end Purelib.Geometry.Rational

end

end

namespace Purelib.Geometry.Rational.Box

/-- Equal corresponding endpoints identify the original rational boxes.

The four scalar equalities identify both original coordinate intervals.
Their retained ordering certificates are proof fields, so kernel proof
irrelevance identifies them after those same endpoints are substituted. -/
public theorem ext {left right : Box}
    (xLower : left.xLower = right.xLower)
    (xUpper : left.xUpper = right.xUpper)
    (yLower : left.yLower = right.yLower)
    (yUpper : left.yUpper = right.yUpper) : left = right := by
  cases left
  cases right
  cases xLower
  cases xUpper
  cases yLower
  cases yUpper
  rfl

end Purelib.Geometry.Rational.Box

section
-- Reusable certificate support retained from the retired quartic fixture programme.

@[expose] public section

namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart1
/-- The original rational box type with ordered endpoints. -/
private abbrev
  Box :=
  Geometry.Rational.Box
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart1

end

section
-- Reusable certificate support retained from the retired quartic fixture programme.

@[expose] public section

namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart2
/-- The original rational box type with ordered endpoints. -/
private abbrev
  Box :=
  Geometry.Rational.Box
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart2

end

section
-- Reusable certificate support retained from the retired quartic fixture programme.

@[expose] public section

namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart3
/-- The original rational box type with ordered endpoints. -/
private abbrev
  Box :=
  Geometry.Rational.Box
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart3

end

section
-- Reusable certificate support retained from the retired quartic fixture programme.

@[expose] public section

namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart4
/-- The original rational box type with ordered endpoints. -/
private abbrev
  Box :=
  Geometry.Rational.Box
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart4

end

section
-- Reusable certificate support retained from the retired quartic fixture programme.

@[expose] public section

namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart5
/-- The original rational box type with ordered endpoints. -/
private abbrev
  Box :=
  Geometry.Rational.Box
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart5

end

section
-- Reusable certificate support retained from the retired quartic fixture programme.

@[expose] public section

namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart6
/-- The original rational box type with ordered endpoints. -/
private abbrev
  Box :=
  Geometry.Rational.Box
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart6

end

section
-- Reusable certificate support retained from the retired quartic fixture programme.

@[expose] public section

namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart7
/-- The original rational box type with ordered endpoints. -/
private abbrev
  Box :=
  Geometry.Rational.Box
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart7

end

section
-- Reusable certificate support retained from the retired quartic fixture programme.

@[expose] public section

namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart1
/-- The original rational box type with ordered endpoints. -/
private abbrev
  Box :=
  Geometry.Rational.Box
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart1

end

section
-- Reusable certificate support retained from the retired quartic fixture programme.

@[expose] public section

namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart2
/-- The original rational box type with ordered endpoints. -/
private abbrev
  Box :=
  Geometry.Rational.Box
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart2

end

section
-- Reusable certificate support retained from the retired quartic fixture programme.

@[expose] public section

namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart3
/-- The original rational box type with ordered endpoints. -/
private abbrev
  Box :=
  Geometry.Rational.Box
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart3

end

section
-- Reusable certificate support retained from the retired quartic fixture programme.

@[expose] public section

namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart4
/-- The original rational box type with ordered endpoints. -/
private abbrev
  Box :=
  Geometry.Rational.Box
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart4

end

section
-- Reusable certificate support retained from the retired quartic fixture programme.

@[expose] public section

namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart5
/-- The original rational box type with ordered endpoints. -/
private abbrev
  Box :=
  Geometry.Rational.Box
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart5

end

section
-- Reusable certificate support retained from the retired quartic fixture programme.

@[expose] public section

namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart6
/-- The original rational box type with ordered endpoints. -/
private abbrev
  Box :=
  Geometry.Rational.Box
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart6

end

section
-- Reusable certificate support retained from the retired quartic fixture programme.

@[expose] public section

namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart7
/-- The original rational box type with ordered endpoints. -/
private abbrev
  Box :=
  Geometry.Rational.Box
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart7

end

section
section
@[expose] public section

/-!
# Finite enclosure representations and direct translations

This module instantiates the generic protocol for rational balls, rational
boxes, boxed raw CCL prefixes, finite fast-Cauchy indices, and states of an
arbitrary progressive enclosure process.
-/

namespace Purelib.CCL.Translation
open Purelib.Data.Gaussian

namespace Ball
end Ball
end Purelib.CCL.Translation

end

end
