import RationalRotations.FiniteKernelApproximation
import RationalRotations.IntroductoryExample

/-!
# Finite kernel-approximation regression requests

These named values exercise the arbitrary-precision constructor on the five
chart shapes called for by the finite density plan.  Each target is requested
at squared radii `1/10` and `1/100`; the returned records themselves retain
the exact error proofs.
-/

namespace RationalRotations

namespace FiniteKernelApproximationExamples

abbrev Scalar := RFAP.ConstructiveFraction.Rational

/-- The identity target, displayed through the projective identity
representative. -/
def identitySource : NonNullProportion Scalar :=
  NonNullProportion.identity ExampleSixtyFour.quarterTurn

/-- A coordinate half-turn target. -/
def halfTurnSource : NonNullProportion Scalar where
  scalar := 0
  vector := ExampleSixtyFour.axis
  normNonzero := by
    change (1 : Scalar) ≠ 0
    decide

/-- The generic all-nonzero target `(2:1:2:3)` from the introduction. -/
def genericSource : NonNullProportion Scalar := IntroductoryExample.proportion

private theorem tenthPositive : (0 : Scalar) < 1 / 10 :=
  RFAP.ConstructiveFraction.div_pos_direct (by decide)
    (RFAP.ConstructiveFraction.natCast_pos_direct (by decide))

private theorem hundredthPositive : (0 : Scalar) < 1 / 100 :=
  RFAP.ConstructiveFraction.div_pos_direct (by decide)
    (RFAP.ConstructiveFraction.natCast_pos_direct (by decide))

def identityTenth :=
  FiniteKernelApproximation.kernelApproximation identitySource.rotation
    ((1 : Scalar) / 10) tenthPositive

def identityHundredth :=
  FiniteKernelApproximation.kernelApproximation identitySource.rotation
    ((1 : Scalar) / 100) hundredthPositive

def halfTurnTenth :=
  FiniteKernelApproximation.kernelApproximation halfTurnSource.rotation
    ((1 : Scalar) / 10) tenthPositive

def halfTurnHundredth :=
  FiniteKernelApproximation.kernelApproximation halfTurnSource.rotation
    ((1 : Scalar) / 100) hundredthPositive

def quarterTurnTenth :=
  FiniteKernelApproximation.kernelApproximation
    ExampleSixtyFour.quarterTurn.rotation ((1 : Scalar) / 10) tenthPositive

def quarterTurnHundredth :=
  FiniteKernelApproximation.kernelApproximation
    ExampleSixtyFour.quarterTurn.rotation ((1 : Scalar) / 100)
      hundredthPositive

def threeFourFiveTenth :=
  FiniteKernelApproximation.kernelApproximation
    ExampleSixtyFour.threeFourFive.rotation ((1 : Scalar) / 10)
      tenthPositive

def threeFourFiveHundredth :=
  FiniteKernelApproximation.kernelApproximation
    ExampleSixtyFour.threeFourFive.rotation ((1 : Scalar) / 100)
      hundredthPositive

def genericTenth :=
  FiniteKernelApproximation.kernelApproximation genericSource.rotation
    ((1 : Scalar) / 10) tenthPositive

def genericHundredth :=
  FiniteKernelApproximation.kernelApproximation genericSource.rotation
    ((1 : Scalar) / 100) hundredthPositive

/-- A small concrete computation guard for the finite refinement and the
base-four square-root bracket. -/
theorem quarterTurnTenth_scale : quarterTurnTenth.scale = 980 := by decide

end FiniteKernelApproximationExamples

end RationalRotations
