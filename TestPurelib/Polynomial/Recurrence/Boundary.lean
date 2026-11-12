module

public import Purelib.Polynomial.Recurrence.Boundary
public import Purelib.Polynomial.Recurrence.Mode
public import Purelib.Polynomial.Dense.Companion.Execution
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic

/-!
# Exact startup, repeated-root and coupled-boundary examples

Each reading runs the original coefficient row on an actual finite mode
window. The expected rows are independent closed rational amounts.
-/

public section

namespace TestPurelib.Polynomial.Recurrence.Boundary

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense (Companion)
open Purelib.Polynomial.Recurrence

/-- The source polynomial z with its original descending coefficient table. -/
@[expose] def z : DensePolynomial Rational := ⟨[1, 0]⟩

/-- The source polynomial z squared with its repeated zero root. -/
@[expose] def zSquared : DensePolynomial Rational := ⟨[1, 0, 0]⟩

/-- The source constant one, including negative-monomial polynomializations. -/
@[expose] def one : DensePolynomial Rational := ⟨[1]⟩

/-- The zeroth zero-root transient on the requested horizon. -/
@[expose] def transient (order count : Nat) : Vec Rational count := Mode.window 0 order count

/-- z has no left startup row at the minimal shift. -/
theorem z_no_boundary : boundary z 0 (transient 0 3) = .nil := rfl

/-- The tail z recurrence kills every reading after its one-coordinate transient. -/
theorem z_transient_tail : row z 0 (transient 0 4) 0 = 0 := by decide

/-- The negative monomial z inverse has an actual zero startup row. -/
theorem inverse_z_startup : sample (boundary one 1 (transient 0 3)) 0 = 0 := by decide

/-- Its first tail row reads the original zeroth input, so no transient survives. -/
theorem inverse_z_tail : row one 1 (transient 0 3) 1 = 1 := by decide

/-- An extra shift for the constant one gives boundary coefficient one. -/
theorem shifted_one : sample (boundary z 1 (transient 0 3)) 0 = 1 := by decide

/-- An extra shift for z leaves the original zeroth transient in the kernel. -/
theorem shifted_z_first : sample (boundary zSquared 1 (transient 0 3)) 0 = 0 := by decide

/-- The same actual row eliminates the extra first-coordinate transient. -/
theorem shifted_z_second : sample (boundary zSquared 1 (transient 1 3)) 0 = 1 := by decide

/-- The larger shift for z inverse retains its original zero first startup row. -/
theorem shifted_inverse_first : sample (boundary z 2 (transient 0 3)) 0 = 0 := by decide

/-- Its second original row eliminates the extra transient. -/
theorem shifted_inverse_second : sample (boundary z 2 (transient 0 3)) 1 = 1 := by decide

/-- The actual polynomialization of z inverse times (z-one-half) squared. -/
@[expose] def repeated : DensePolynomial Rational := ⟨[1, -1, 1 / 4]⟩

/-- The ordinary repeated-root mode contributes minus one half to the startup row. -/
theorem repeated_first : sample (boundary repeated 1 (Mode.window (1 / 2) 0 3)) 0 = -1 / 2 := by decide

/-- Its genuine generalized mode contributes one to that same row. -/
theorem repeated_second : sample (boundary repeated 1 (Mode.window (1 / 2) 1 3)) 0 = 1 := by decide

/-- The two generalized coordinates combine to an actual kernel horizon. -/
@[expose] def repeatedKernel : Vec Rational 5 :=
  Vec.zipWith (fun first second => first + (1 / 2) * second)
    (Mode.window (1 / 2) 0 5) (Mode.window (1 / 2) 1 5)

/-- The retained repeated-root kernel vector satisfies the original startup row. -/
theorem repeated_kernel_boundary : sample (boundary repeated 1 repeatedKernel) 0 = 0 := by decide

/-- The same actual kernel horizon satisfies its first complete tail recurrence. -/
theorem repeated_kernel_tail : row repeated 1 repeatedKernel 1 = 0 := by decide

/-- The coupled source polynomial (z-one-quarter)(z-one-half)(z-two). -/
@[expose] def coupled : DensePolynomial Rational := ⟨[1, -11 / 4, 13 / 8, -1 / 4]⟩

/-- The first inside mode contributes one to the actual coupled startup row. -/
theorem coupled_first : sample (boundary coupled 1 (Mode.window (1 / 4) 0 5)) 0 = 1 := by decide

/-- The second inside mode contributes one half, rather than coordinate-selection weight one. -/
theorem coupled_second : sample (boundary coupled 1 (Mode.window (1 / 2) 0 5)) 0 = 1 / 2 := by decide

/-- The displayed coupled kernel uses both actual inside modes. -/
@[expose] def coupledKernel : Vec Rational 5 :=
  Vec.zipWith (fun first second => (-1 / 2) * first + second)
    (Mode.window (1 / 4) 0 5) (Mode.window (1 / 2) 0 5)

/-- The coupled kernel horizon satisfies its actual original startup row. -/
theorem coupled_kernel_boundary : sample (boundary coupled 1 coupledKernel) 0 = 0 := by decide

/-- Its first complete tail also satisfies the independently generated recurrence. -/
theorem coupled_kernel_tail : row coupled 1 coupledKernel 1 = 0 := by decide

/-- A conventional z Toeplitz rectangle has its nonzero entry below the diagonal. -/
theorem z_toeplitz_below : toeplitz z 0 2 2 1 0 = 1 := by decide

/-- The plus-shift z rectangle has the transposed entry above the diagonal. -/
theorem z_plus_above : plus z 0 2 2 0 1 = 1 := by decide

/-- The automatic original companion of z. -/
@[expose] def zCompanion : Companion z := Companion.ofPositive z (by decide)

/-- An actual nonzero initial state for the zero-root companion. -/
@[expose] def zState : Vec Rational z.natDegree := .cons 7 .nil

/-- The zero-root companion retains its actual initial reading. -/
theorem z_companion_initial : zCompanion.reading zState 0 = 7 := by decide

/-- Its next original cached-matrix transition kills that transient. -/
theorem z_companion_next : zCompanion.reading zState 1 = 0 := by decide

/-- Further finite transitions do not revive a killed zero-root transient. -/
theorem z_companion_later : zCompanion.reading zState 4 = 0 := by decide

/-- The automatic original companion of the repeated-root source. -/
@[expose] def repeatedCompanion : Companion repeated := Companion.ofPositive repeated (by decide)

/-- The retained initial coordinates of the actual repeated-root kernel. -/
@[expose] def repeatedState : Vec Rational repeated.natDegree := .cons 1 (.cons 1 .nil)

/-- Cached companion execution produces the generalized repeated-root reading. -/
theorem repeated_companion_later : repeatedCompanion.reading repeatedState 2 = 3 / 4 := by decide

/-- Its actual execution window satisfies the original startup boundary. -/
theorem repeated_companion_boundary :
    sample (boundary repeated 1 (repeatedCompanion.window repeatedState 5)) 0 = 0 := by decide

/-- The automatic companion retains the original coupled source. -/
@[expose] def coupledCompanion : Companion coupled := Companion.ofPositive coupled (by decide)

/-- The actual initial coordinates of the coupled kernel mode combination. -/
@[expose] def coupledState : Vec Rational coupled.natDegree :=
  .cons (1 / 2) (.cons (3 / 8) (.cons (7 / 32) .nil))

/-- Cached original companion execution gives the coupled kernel's next exact reading. -/
theorem coupled_companion_later : coupledCompanion.reading coupledState 3 = 15 / 128 := by
  change coupledCompanion.reading coupledState coupled.natDegree = 15 / 128
  rw [Companion.reading_degree, Companion.step_last]
  change (1 / 4 : Rational) * (1 / 2) +
    ((-13 / 8) * (3 / 8) + ((11 / 4) * (7 / 32) + 0)) = 15 / 128
  decide +kernel

/-- The original startup row vanishes on the actual coupled execution window. -/
theorem coupled_companion_boundary :
    sample (boundary coupled 1 (coupledCompanion.window coupledState 5)) 0 = 0 := by decide

/-- That same retained execution window satisfies its first complete original tail row. -/
theorem coupled_companion_tail : row coupled 1 (coupledCompanion.window coupledState 5) 1 = 0 := by decide

end TestPurelib.Polynomial.Recurrence.Boundary
