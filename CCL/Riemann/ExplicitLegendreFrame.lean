import CCL.Progressive.SquarefreeEvaluation
import CCL.Riemann.LegendrePaths

/-!
# One explicit rational Legendre root frame

This module constructs the base fibre at `lambda = 2` from three displayed
rational winding-one boxes around `0`, `1`, and `2`.  The chamber owners,
logical root labels, and left-to-right projection order all come from the same
finite boxes.  No generic owner ordering is guessed after isolation.
-/

namespace CCL.Riemann.ExplicitLegendreFrame

open CCL.Riemann.LegendrePaths

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev LocalOwner := CCL.ProgressivePolynomialRoots.LocalOwner
abbrev CoefficientState :=
  CCL.ProgressivePolynomialRoots.CoefficientState
abbrev CoefficientTable :=
  CCL.ProgressivePolynomialRoots.CoefficientTable

/-- The rational base parameter used by the concrete pilot. -/
def parameter : Gaussian := 2

/-- One affine factor `x - root`. -/
def factor (root : Gaussian) : GaussianPolynomial :=
  RFAP.AffineWinding.translatedCoordinate root

/-- The displayed factorization in logical root order. -/
def factors : GaussianPolynomial :=
  (factor 0 * factor parameter) * factor 1

theorem polynomial_eq_factors : polynomial parameter = factors := by
  decide

/-- A small square centred at a displayed real root. -/
def rootBox (x : Coordinate) : Box :=
  { xLower := x - 1 / 4
    xUpper := x + 1 / 4
    yLower := -(1 / 4)
    yUpper := 1 / 4
    x_valid := by
      apply le_of_lt
      calc
        x - 1 / 4 < x := by
          simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
            (by decide : (0 : Coordinate) < 1 / 4) x
        _ < x + 1 / 4 := by
          simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
            (by decide : (0 : Coordinate) < 1 / 4) x
    y_valid := by
      change (-(1 / 4 : Coordinate)) ≤ 1 / 4
      decide }

theorem rootBox_proper (x : Coordinate) : (rootBox x).Proper := by
  constructor
  · change x - 1 / 4 < x + 1 / 4
    calc
      x - 1 / 4 < x := by
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 4) x
      _ < x + 1 / 4 := by
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 4) x
  · change (-(1 / 4 : Coordinate)) < 1 / 4
    decide

def selfClearance (x : Coordinate) :
    RFAP.BoxClearance.BoundaryClearance
      (factor (gaussian x 0)) (rootBox x) :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearanceBox
    (gaussian x 0)
    (by
      unfold rootBox gaussian
      simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
        (by decide : (0 : Coordinate) < 1 / 4) x)
    (by
      unfold rootBox gaussian
      simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
        (by decide : (0 : Coordinate) < 1 / 4) x)
    (by
      change (-(1 / 4 : Coordinate)) < 0
      decide)
    (by
      change (0 : Coordinate) < 1 / 4
      decide)

def leftClearance (root box : Coordinate) (separated : root < box - 1 / 4) :
    RFAP.BoxClearance.BoundaryClearance
      (factor (gaussian root 0)) (rootBox box) :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearance_of_left
    (gaussian root 0) separated

def rightClearance (root box : Coordinate) (separated : box + 1 / 4 < root) :
    RFAP.BoxClearance.BoundaryClearance
      (factor (gaussian root 0)) (rootBox box) :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearance_of_right
    (gaussian root 0) separated

def factorsClearanceZero :
    RFAP.BoxClearance.BoundaryClearance factors (rootBox 0) :=
  RFAP.BoxClearance.BoundaryClearance.mul
    (RFAP.BoxClearance.BoundaryClearance.mul
      (selfClearance 0)
      (rightClearance 2 0 (by decide)))
    (rightClearance 1 0 (by decide))

def factorsClearanceParameter :
    RFAP.BoxClearance.BoundaryClearance factors (rootBox 2) :=
  RFAP.BoxClearance.BoundaryClearance.mul
    (RFAP.BoxClearance.BoundaryClearance.mul
      (leftClearance 0 2 (by decide))
      (selfClearance 2))
    (leftClearance 1 2 (by decide))

def factorsClearanceOne :
    RFAP.BoxClearance.BoundaryClearance factors (rootBox 1) :=
  RFAP.BoxClearance.BoundaryClearance.mul
    (RFAP.BoxClearance.BoundaryClearance.mul
      (leftClearance 0 1 (by decide))
      (rightClearance 2 1 (by decide)))
    (selfClearance 1)

def polynomialClearanceZero :
    RFAP.BoxClearance.BoundaryClearance (polynomial parameter) (rootBox 0) := by
  rw [polynomial_eq_factors]
  exact factorsClearanceZero

def polynomialClearanceParameter :
    RFAP.BoxClearance.BoundaryClearance
      (polynomial parameter) (rootBox 2) := by
  rw [polynomial_eq_factors]
  exact factorsClearanceParameter

def polynomialClearanceOne :
    RFAP.BoxClearance.BoundaryClearance (polynomial parameter) (rootBox 1) := by
  rw [polynomial_eq_factors]
  exact factorsClearanceOne

theorem windingZero :
    RFAP.Winding.quadrupledBoxWinding (polynomial parameter) (rootBox 0) = 4 :=
  by decide

theorem windingParameter :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial parameter) (rootBox 2) = 4 := by
  decide

theorem windingOne :
    RFAP.Winding.quadrupledBoxWinding (polynomial parameter) (rootBox 1) = 4 :=
  by decide

def zeroOwner : LocalOwner (polynomial parameter) where
  box := rootBox 0
  proper := rootBox_proper 0
  clearance := polynomialClearanceZero
  rawWindingFour := windingZero

def parameterOwner : LocalOwner (polynomial parameter) where
  box := rootBox 2
  proper := rootBox_proper 2
  clearance := polynomialClearanceParameter
  rawWindingFour := windingParameter

def oneOwner : LocalOwner (polynomial parameter) where
  box := rootBox 1
  proper := rootBox_proper 1
  clearance := polynomialClearanceOne
  rawWindingFour := windingOne

def owner : Fin 3 -> LocalOwner (polynomial parameter)
  | 0 => zeroOwner
  | 1 => parameterOwner
  | 2 => oneOwner

private theorem finThree_cases (index : Fin 3) :
    index = 0 ∨ index = 1 ∨ index = 2 := by
  rcases index with ⟨value, bound⟩
  omega0

theorem owner_pairwise : forall left right : Fin 3, left ≠ right ->
    (owner left).box.Separated (owner right).box := by
  intro left right different
  rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
    subst right <;>
    first | exact (different rfl).elim | decide

def ownerFamily :
    CCL.ProgressivePolynomialRoots.OwnerFamily (polynomial parameter) 3 where
  owner := owner
  pairwiseSeparated := owner_pairwise

/-- A terminating coefficient channel read at its unique exact state. -/
def exactCoefficientState (value : Gaussian) : CoefficientState where
  channel := CCL.ProgressiveCoherence.CoherentNamed.exact value
  state := ()

@[simp] theorem exactCoefficientState_value (value : Gaussian) :
    (exactCoefficientState value).value = value := rfl

@[simp] theorem exactCoefficientState_allowance (value : Gaussian) :
    (exactCoefficientState value).allowance = 0 := rfl

def coefficientValues : List Gaussian :=
  [-(1 + parameter), parameter, 0]

def coefficientTable : CoefficientTable where
  entries := coefficientValues.map exactCoefficientState

@[simp] theorem coefficientTable_degree : coefficientTable.degree = 3 := rfl

@[simp] theorem coefficientTable_polynomial :
    coefficientTable.polynomial = polynomial parameter := rfl

theorem coefficientTable_allowances_lt {target : Coordinate}
    (positive : 0 < target) :
    CCL.ProgressivePolynomialRoots.CoefficientTable.AllowancesLt
      coefficientTable.entries target := by
  simp only [coefficientTable, coefficientValues, List.map_cons, List.map_nil,
    CCL.ProgressivePolynomialRoots.CoefficientTable.AllowancesLt,
    exactCoefficientState_allowance]
  exact ⟨positive, positive, positive, trivial⟩

/-- Explicit parameterized Bezout coefficients for a Legendre cubic. -/
def bezoutLeftAt (lambda : Gaussian) : GaussianPolynomial :=
  ⟨[-6 * (lambda ^ 2 - lambda + 1),
    (lambda + 1) * (4 * lambda ^ 2 - 7 * lambda + 4)]⟩

def bezoutRightAt (lambda : Gaussian) : GaussianPolynomial :=
  ⟨[2 * (lambda ^ 2 - lambda + 1),
    -(lambda + 1) * (2 * lambda ^ 2 - 3 * lambda + 2),
    lambda * (lambda - 1) ^ 2]⟩

theorem derivative_eval (lambda point : Gaussian) :
    (RFAP.ConstructiveGCD.derivative (polynomial lambda)).eval point =
      3 * point * point - 2 * (lambda + 1) * point + lambda := by
  unfold RFAP.ConstructiveGCD.derivative
  rw [RFAP.ComputableDerivative.eval_derivative]
  unfold polynomial
    RFAP.ComputableDerivative.evalDerivativeCoeffs
    RFAP.ComputableDerivative.evalDerivativeStep
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

theorem bezout_identity (lambda point : Gaussian) :
    (bezoutLeftAt lambda).eval point * (polynomial lambda).eval point +
        (bezoutRightAt lambda).eval point *
          (RFAP.ConstructiveGCD.derivative
            (polynomial lambda)).eval point = lambda ^ 2 * (lambda - 1) ^ 2 := by
  rw [polynomial_eval, derivative_eval]
  unfold bezoutLeftAt bezoutRightAt
    RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- Finite squarefreeness for every displayed Legendre parameter whose
explicit discriminant-like unit is nonzero. -/
def squarefreeAt (lambda : Gaussian)
    (unitNonzero : lambda ^ 2 * (lambda - 1) ^ 2 ≠ 0) :
    RFAP.Squarefree.SquarefreeCertificate (polynomial lambda) :=
  CCL.ProgressiveSquarefree.ofEvalBezoutUnit
    (polynomial lambda) (polynomial_isZero lambda)
    (lambda ^ 2 * (lambda - 1) ^ 2) unitNonzero
    (bezoutLeftAt lambda) (bezoutRightAt lambda) (bezout_identity lambda)

/-- The finite squarefreeness calculation for the displayed cubic. -/
def squarefree :
    RFAP.Squarefree.SquarefreeCertificate coefficientTable.polynomial := by
  rw [coefficientTable_polynomial]
  exact squarefreeAt parameter (by decide)

def isolationInput : RFAP.BoxFTA.Input coefficientTable.polynomial where
  squarefree := squarefree
  degreeAtLeastTwo := by decide

/-- The exact root chamber.  The three local owners are the displayed boxes;
the independent finite RFAP supplies only the degree-sharp maximality law. -/
def chamberFrame : CCL.FiniteMonodromy.ChamberFrame where
  reference := coefficientTable
  chamber :=
    { degreeAtLeastTwo := by decide
      squarefree := squarefree
      owners := ownerFamily
      referenceSmall := coefficientTable_allowances_lt
        (CCL.ProgressivePolynomialRoots.simpleRootChamberTarget_pos
          coefficientTable squarefree ownerFamily)
      referenceMaximality :=
        (CCL.BoxRFAPBridge.prove isolationInput).boxes.maximality }

@[simp] theorem chamberFrame_polynomial :
    chamberFrame.polynomial = polynomial parameter := rfl

@[simp] theorem chamberFrame_owner_box (position : Fin 3) :
    (chamberFrame.owner position).box = (owner position).box := rfl

/-- Projection positions `0,1,2` correspond to the real root order
`0,1,lambda`; logical labels remain `0,lambda,1`. -/
def projectionOrder : CCL.FiniteMonodromy.FiniteBijection 3 3 where
  forward
    | 0 => 0
    | 1 => 2
    | 2 => 1
  backward
    | 0 => 0
    | 1 => 2
    | 2 => 1
  backward_forward := by
    intro position
    rcases finThree_cases position with positionZero | positionOne |
      positionTwo <;> subst position <;> rfl
  forward_backward := by
    intro position
    rcases finThree_cases position with positionZero | positionOne |
      positionTwo <;> subst position <;> rfl

def projectionOwner : Fin 3 -> LocalOwner (polynomial parameter)
  | 0 => zeroOwner
  | 1 => oneOwner
  | 2 => parameterOwner

@[simp] theorem projectionOwner_eq_owner_projectionOrder
    (position : Fin 3) :
    (projectionOwner position).box =
      (owner (projectionOrder.forward position)).box := by
  rcases finThree_cases position with positionZero | positionOne |
    positionTwo <;> subst position <;> rfl

/-- The concrete Legendre frame at `lambda = 2`. -/
def frame : Frame parameter where
  chamber := chamberFrame
  polynomial_eq := rfl
  labels := CCL.FiniteMonodromy.FiniteBijection.identity 3
  owner_contains := by
    intro label
    rcases finThree_cases label with labelZero | labelOne | labelTwo <;>
      subst label <;> decide
  projectionOrder := projectionOrder
  projectionOwner := fun position =>
    CCL.FiniteMonodromy.castOwner chamberFrame_polynomial.symm
      (projectionOwner position)
  projection_refines := by
    intro position
    change (projectionOwner position).box.Refines
      (chamberFrame.owner (projectionOrder.forward position)).box
    rw [projectionOwner_eq_owner_projectionOrder,
      chamberFrame_owner_box]
    exact RFAP.Boxes.Box.refines_refl
      (owner (projectionOrder.forward position)).box
  projection_xOrdered := by
    intro left right order
    rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
      subst left <;>
      rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
      subst right <;>
      simp only [Fin.isValue, CCL.FiniteMonodromy.castOwner_box] at order ⊢ <;>
      first | omega0 | decide

@[simp] theorem frame_owner_zero_contains :
    (frame.chamber.owner (frame.labels.forward 0)).box.Contains 0 := by
  decide

@[simp] theorem frame_owner_parameter_contains :
    (frame.chamber.owner (frame.labels.forward 1)).box.Contains parameter := by
  decide

@[simp] theorem frame_owner_one_contains :
    (frame.chamber.owner (frame.labels.forward 2)).box.Contains 1 := by
  decide

end CCL.Riemann.ExplicitLegendreFrame
