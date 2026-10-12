module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Data.Vector.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State

open Purelib.LinearAlgebra.Matrix

open Purelib.Riemann.Integration

section
@[expose] public section

/-!
# Retryable acquisition of Legendre fractional denominators

The generic division preflight is reused at the exact transformed denominator.
A successful retained-state search is converted to the generalized modular
preparation by carrying its based denominator, whole-ball apartness, and
operational equivalence to the original process.
-/

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition

/-- Retained generic division state specialized to one exact fractional denominator. -/
abbrev State (matrix :
  IntegralMatrix) (tau : Coherent.CoherentNamed) :=
  Name.Coherent.Refinement.State (LegendreModularMonodromy.fractionalDenominator matrix tau)

namespace State

/-- Initial state of the bounded transformed-denominator search. -/
def initial (matrix :
  IntegralMatrix) (tau : Coherent.CoherentNamed) :
    State matrix tau :=
  Name.Coherent.Refinement.State.initial
    (LegendreModularMonodromy.fractionalDenominator matrix tau)

/-- Finite reachability consists solely of actual generic-division refinement steps. -/
abbrev Reachable {matrix :
  IntegralMatrix} {tau : Coherent.CoherentNamed}
    (first last : State matrix tau) :=
  Name.Coherent.Refinement.State.Reachable first last

end State

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition

end

section
@[expose] public section

/-!
# Automatic finite-word dual period outputs

The public result caches the exact word matrix, its denominator preparation,
and the productive output. A positive enclosure constructs it directly;
bounded acquisition returns either this same result or an exact resumable
state. The transport proof is shared by both construction routes.
-/

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.State

set_option genInjectivity false in
/-- Retained data for one already folded finite word. -/
structure StatePayload (specification
  : IntegralMatrix → Prop)
    (searchType : IntegralMatrix → Type) where
  /-- The exact folded integral matrix retained by this state. -/ matrix : IntegralMatrix
  /-- The retained matrix satisfies the original matrix specification. -/ matrix_eq : specification matrix
  /-- The retained search data indexed by that exact folded matrix. -/ search : searchType matrix

constructive_injectivity StatePayload

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.State

end
