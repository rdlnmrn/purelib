import RationalRotations.PositiveSquareClassSignatures

/-!
# Executable examples of positive rational square-class signatures

These small kernel-checked calculations exercise square removal in the finite
factorizer used by `PositiveSquareClassSignatures.compute`.
-/

namespace RationalRotations

namespace PositiveSquareClassSignatureExamples

open RFAP.ConstructivePrimeParity

theorem one_kernel : oddPrimeKernel 1 = 1 := by
  decide +kernel

theorem eight_kernel : oddPrimeKernel 8 = 2 := by
  decide +kernel

theorem twelve_kernel : oddPrimeKernel 12 = 3 := by
  decide +kernel

theorem eighteen_kernel : oddPrimeKernel 18 = 2 := by
  decide +kernel

theorem seventyTwo_kernel : oddPrimeKernel 72 = 2 := by
  decide +kernel

end PositiveSquareClassSignatureExamples

end RationalRotations
