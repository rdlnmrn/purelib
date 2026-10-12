module
public import Purelib.Data.Rat.Fraction

open Purelib.Data.Rat

section
@[expose] public section
namespace Purelib.Data.Rat.Fraction.Basic

/-- The canonical quotient-free rational carrier, retained as an exact reducible alias. -/
abbrev Rational := Purelib.Data.Rat.Fraction.Rational
end Purelib.Data.Rat.Fraction.Basic

end

section
section
@[expose] public section
namespace Purelib.Data.Rat.Fraction.Basic

/-! ## Canonical finite representatives -/

/-- The canonical rational carrier itself, with its retained reduced numerator and denominator. -/
abbrev ReducedFraction := Fraction.Rational
end Purelib.Data.Rat.Fraction.Basic
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.Rat.Fraction.Basic

/-- View a canonical rational as its identical reduced working record. -/
def ofRational (source : Fraction.Rational) : Fraction.Basic.ReducedFraction :=
  source
end Purelib.Data.Rat.Fraction.Basic
end

end

section
section
@[expose] public section
namespace Purelib.Data.Rat.Fraction.Basic

/-- Read the reduced record already retained by a canonical rational. -/
def representative (value : Fraction.Rational) : Fraction.Basic.ReducedFraction
  := value
end Purelib.Data.Rat.Fraction.Basic
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.Rat.Fraction.Basic

/-- Rebuild a rational from its already retained canonical representative. -/
def canonical (value : Fraction.Rational) : Fraction.Rational :=
  Fraction.Basic.representative value
end Purelib.Data.Rat.Fraction.Basic
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.Rat.Fraction.Basic

/-- Rebuilding the retained canonical representative leaves the rational unchanged. -/
theorem canonical_eq (value : Fraction.Rational) : Fraction.Basic.canonical value
  = value := rfl
end Purelib.Data.Rat.Fraction.Basic
end
end

end

section
section
@[expose] public section
namespace Purelib.Data.Rat.Fraction.Basic

/-- Read a reduced working record as the identical canonical rational value. -/
def value (fraction : Fraction.Basic.ReducedFraction) : Fraction.Rational :=
  fraction
end Purelib.Data.Rat.Fraction.Basic
end

end

section
section
@[expose] public section
namespace Purelib.Data.Rat.Fraction.Basic

/-- Reading the value of a rational's reduced record returns that rational. -/
theorem value_ofRational (source : Fraction.Rational) :
    Fraction.Basic.value (Fraction.Basic.ofRational source) = source := rfl
end Purelib.Data.Rat.Fraction.Basic
end

end

section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticABackwardSampleCertificates

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticABackwardSampleCertificates
end

end

section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticABackwardSampleSumCertificates

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticABackwardSampleSumCertificates
end

end

section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticBBackwardPreparedSampleBridge
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev Coordinate := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticBBackwardPreparedSampleBridge
end

end

section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticBBackwardPreparedSampleBridge

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticBBackwardPreparedSampleBridge
end

end

section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticBBackwardSampleCertificates

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticBBackwardSampleCertificates
end

end

section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticBBackwardSampleSumCertificates

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticBBackwardSampleSumCertificates
end

end

section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticBForwardPreparedSampleBridge
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev Coordinate := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticBForwardPreparedSampleBridge
end

end

section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticBForwardPreparedSampleBridge

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticBForwardPreparedSampleBridge
end

end

section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticBForwardSampleCertificates

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticBForwardSampleCertificates
end

end

section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticBForwardSampleSumCertificates

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticBForwardSampleSumCertificates
end

end

section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticCycleSampleCertificates

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational

end Purelib.Examples.Riemann.ExplicitQuarticCycleSampleCertificates
end

end

section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticHorizontalSampleCertificates

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticHorizontalSampleCertificates
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticHorizontalSampleSumCertificates

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticHorizontalSampleSumCertificates
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedABackwardHorizontalSecond
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev Coordinate := Fraction.Rational

end Purelib.Examples.Riemann.ExplicitQuarticPreparedABackwardHorizontalSecond
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedABackwardHorizontalSecond

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedABackwardHorizontalSecond
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedBBackwardCompletionPart2
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev Coordinate :=
  Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedBBackwardCompletionPart2
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedBBackwardCompletionPart3
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev Coordinate :=
  Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedBBackwardCompletionPart3
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedBBackwardCompletionPart4
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev Coordinate :=
  Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedBBackwardCompletionPart4
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedBBackwardCompletionPart5
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev Coordinate :=
  Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedBBackwardCompletionPart5
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedBForwardCompletionPart2
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev Coordinate :=
  Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedBForwardCompletionPart2
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedBForwardCompletionPart3
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev Coordinate :=
  Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedBForwardCompletionPart3
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedBForwardCompletionPart4
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev Coordinate :=
  Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedBForwardCompletionPart4
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedEighthCell

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedEighthCell
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedEighthCellCertificate

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedEighthCellCertificate
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedFifthCell

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedFifthCell
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedFifthCellCertificate

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedFifthCellCertificate
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedFourthCell

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedFourthCell
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedFourthCellCertificate

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedFourthCellCertificate
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedHorizontalCells
/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedHorizontalCells
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCell

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCell
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCellCertificate

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational

end Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCellCertificate
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCellCompletion

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational

end Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCellCompletion
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCellFirstRecenter

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational

end Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCellFirstRecenter
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCellGrid

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCellGrid
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCellRecenter

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational

end Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCellRecenter
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCellRetained

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational

end Purelib.Examples.Riemann.ExplicitQuarticPreparedSecondCellRetained
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSeventhCell

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedSeventhCell
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSeventhCellCertificate

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedSeventhCellCertificate
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSixthCell

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedSixthCell
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSixthCellCertificate

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedSixthCellCertificate
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedThirdCell

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedThirdCell
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedThirdCellCertificate

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational
end Purelib.Examples.Riemann.ExplicitQuarticPreparedThirdCellCertificate
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedVerticalTail

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational

end Purelib.Examples.Riemann.ExplicitQuarticPreparedVerticalTail
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.PreparedEightStepResetAtThree
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev Coordinate := Fraction.Rational
end Purelib.Examples.Riemann.PreparedEightStepResetAtThree
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.PreparedGeneratedReset

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev Q := Fraction.Rational

end Purelib.Examples.Riemann.PreparedGeneratedReset
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.PreparedSurfaceCoercivityExamples

/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev Coordinate := Fraction.Rational
end Purelib.Examples.Riemann.PreparedSurfaceCoercivityExamples
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart1
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev
  Coordinate
  := Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart1
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart1

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev
  Q :=
  Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart1
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart2
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev
  Coordinate
  := Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart2
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart2

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev
  Q :=
  Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart2
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart3
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev
  Coordinate
  := Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart3
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart3

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev
  Q :=
  Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart3
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart4
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev
  Coordinate
  := Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart4
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart4

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev
  Q :=
  Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart4
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart5
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev
  Coordinate
  := Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart5
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart5

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev
  Q :=
  Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart5
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart6
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev
  Coordinate
  := Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart6
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart6

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev
  Q :=
  Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart6
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart7
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev
  Coordinate
  := Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart7
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart7

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev
  Q :=
  Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedALeftSampleCertificatesPart7
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart1
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev
  Coordinate
  := Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart1
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart1

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev
  Q :=
  Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart1
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart2
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev
  Coordinate
  := Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart2
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart2

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev
  Q :=
  Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart2
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart3
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev
  Coordinate
  := Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart3
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart3

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev
  Q :=
  Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart3
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart4
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev
  Coordinate
  := Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart4
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart4

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev
  Q :=
  Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart4
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart5
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev
  Coordinate
  := Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart5
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart5

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev
  Q :=
  Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart5
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart6
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev
  Coordinate
  := Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart6
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart6

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev
  Q :=
  Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart6
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart7
/-- The exact canonical rational carrier used for the local coordinates. -/
private abbrev
  Coordinate
  := Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart7
end

end

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
@[expose] public section
namespace Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart7

/-- The exact canonical rational carrier used by the local scalar notation. -/
private abbrev
  Q :=
  Fraction.Rational
end Purelib.Examples.Riemann.QuarticPrepared.Generated.ExplicitQuarticPreparedARightSampleCertificatesPart7
end

end
