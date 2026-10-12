module

public import Purelib.NumberTheory.Prime.Parity
import Purelib.NumberTheory.SquareClass.Rational.Signature

open Purelib.NumberTheory

@[expose] public section

/-!
# Executable examples of positive rational square-class signatures

These small kernel-checked calculations exercise square removal in the finite
factorizer used by `PositiveSquareClassSignatures.compute`.
-/

namespace formalisations.RationalRotations.Chapters

namespace PositiveSquareClassSignatureExamples

open Purelib.NumberTheory.Prime.Parity

/-- The odd-prime kernel of one is one. -/
theorem one_kernel : Prime.Parity.oddPrimeKernel 1 = 1 := by
  decide +kernel

/-- Removing square factors from eight leaves odd-prime kernel two. -/
theorem eight_kernel : Prime.Parity.oddPrimeKernel 8 = 2 := by
  decide +kernel

/-- Removing square factors from twelve leaves odd-prime kernel three. -/
theorem twelve_kernel : Prime.Parity.oddPrimeKernel 12 = 3 := by
  decide +kernel

/-- Removing square factors from eighteen leaves odd-prime kernel two. -/
theorem eighteen_kernel : Prime.Parity.oddPrimeKernel 18 = 2 := by
  decide +kernel

/-- Removing square factors from seventy-two leaves odd-prime kernel two. -/
theorem seventyTwo_kernel : Prime.Parity.oddPrimeKernel 72 = 2 := by
  decide +kernel

end PositiveSquareClassSignatureExamples

end formalisations.RationalRotations.Chapters
