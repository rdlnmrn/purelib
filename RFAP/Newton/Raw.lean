import RFAP.Isolation.RawSubdivision
import RFAP.Isolation.LocalExtraction

/-!
# Choice-free refinement to a certified Newton point

The raw nonzero-winding subdivision is iterated to a coefficient-computed
positive diagonal threshold.  Its explicit contraction bound then supplies
the small residual required by the finite Bézout derivative argument.
-/

namespace RFAP.RawNewton

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance
abbrev AxisEliminationCertificate :=
  RFAP.AxisSafeCuts.AxisEliminationCertificate
abbrev SquarefreeCertificate :=
  RFAP.LocalExtraction.SquarefreeCertificate
abbrev RawWindingState := RFAP.RawSubdivision.RawWindingState
abbrev NewtonCenterCertificate :=
  RFAP.LocalExtraction.NewtonCenterCertificate

open RFAP.PolynomialBounds
open RFAP.LocalExtraction
open RFAP.RawSubdivision

/-- Positive squared-diagonal target that makes the raw anchor residual small
enough for the finite Bézout derivative separation. -/
def newtonDiagonalThreshold
    (p : GaussianPolynomial) (ambient : Box)
    (squarefree : SquarefreeCertificate p) : Coordinate :=
  derivativeThreshold squarefree ambient / denseLipschitzBound p ambient

theorem newtonDiagonalThreshold_pos
    (p : GaussianPolynomial) (ambient : Box)
    (squarefree : SquarefreeCertificate p) :
    0 < newtonDiagonalThreshold p ambient squarefree :=
  RFAP.ConstructiveFraction.div_pos_direct
    (derivativeThreshold_pos squarefree ambient)
    (denseLipschitzBound_pos p ambient)

/-- Deterministically refine raw winding until the Newton residual threshold
is guaranteed. -/
def refineForNewton
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (squarefree : SquarefreeCertificate p)
    (state : RawWindingState p ambient) : RawWindingState p ambient :=
  refineTo elimination state
    (newtonDiagonalThreshold p ambient squarefree)

theorem refineForNewton_refines
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (squarefree : SquarefreeCertificate p)
    (state : RawWindingState p ambient) :
    (refineForNewton elimination squarefree state).box.Refines state.box :=
  refineTo_refines elimination state
    (newtonDiagonalThreshold p ambient squarefree)

theorem refineForNewton_residualBound_le
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (squarefree : SquarefreeCertificate p)
    (state : RawWindingState p ambient) :
    anchorResidualBound p ambient
        (refineForNewton elimination squarefree state).box ≤
      derivativeThreshold squarefree ambient := by
  let refined := refineForNewton elimination squarefree state
  have diagonal := refineTo_diagonalSq_le elimination state
    (newtonDiagonalThreshold_pos p ambient squarefree)
  have lipschitzPositive := denseLipschitzBound_pos p ambient
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    diagonal lipschitzPositive.le
  change denseLipschitzBound p ambient * refined.box.diagonalSq ≤
    derivativeThreshold squarefree ambient
  calc
    denseLipschitzBound p ambient * refined.box.diagonalSq ≤
        denseLipschitzBound p ambient *
          newtonDiagonalThreshold p ambient squarefree := scaled
    _ = derivativeThreshold squarefree ambient := by
      rw [RFAP.ConstructiveFraction.mul_comm]
      exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne
        (derivativeThreshold squarefree ambient)
        (denseLipschitzBound p ambient) (ne_of_gt lipschitzPositive)

/-- The complete output at the first certified Newton scale. -/
structure Output
    (p : GaussianPolynomial) (ambient : Box)
    (squarefree : SquarefreeCertificate p) where
  state : RawWindingState p ambient
  newton : NewtonCenterCertificate p ambient state.box squarefree

/-- One finite raw subdivision followed by the certified local Newton step. -/
def extractNewton
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreePositive : 0 < p.natDegree)
    (elimination : AxisEliminationCertificate p degreeBound)
    (squarefree : SquarefreeCertificate p)
    (state : RawWindingState p ambient) : Output p ambient squarefree := by
  let refined := refineForNewton elimination squarefree state
  exact
    { state := refined
      newton := computeNewtonCenterOfRawWinding p degreePositive squarefree
        refined.refinesAmbient refined.proper refined.rawWinding_ne
        (refineForNewton_residualBound_le elimination squarefree state) }

end RFAP.RawNewton
