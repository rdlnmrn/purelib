import CCL.Riemann.CertifiedSquareRoot
import CCL.Riemann.AlgebraicDifferentials

/-!
# Finite same-owner square-root continuation chains

A root at each rational sample cannot be selected independently: the two
owners may be permuted by the isolator.  Here a sheet begins at one of the two
explicit power-polynomial owners and every subsequent owner is obtained by a
finite Rouché move from the preceding one.  The inductive chain is itself the
finite certificate that no pointwise re-indexing occurred.
-/

namespace CCL.Riemann.SquareRootContinuationChain

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Box := RFAP.Boxes.Box
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack

/-- One square-root owner at one displayed nonzero radicand.  The ambient box
is existential data only in the constructive `Type` sense: both it and its
track are stored and executable. -/
structure Owner (parameter : Gaussian) where
  parameterNonzero : parameter ≠ 0
  ambient : Box
  track : WindingOneTrack
    (CCL.PowerMonodromy.polynomial parameter
      CCL.Riemann.SquareRootSheets.degreeTwo) ambient

namespace Owner

private abbrev rootPolynomial (parameter : Gaussian) :=
  CCL.PowerMonodromy.polynomial parameter
    CCL.Riemann.SquareRootSheets.degreeTwo

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.ConstructiveGaussian.Gaussian
open RFAP.PathPolynomial
open RFAP.Winding

private def linearPolynomial (slope intercept : Coordinate) : Polynomial :=
  ⟨[slope, intercept]⟩

@[simp] private theorem eval_linearPolynomial
    (slope intercept value : Coordinate) :
    (linearPolynomial slope intercept).eval value = slope * value + intercept := by
  simp [linearPolynomial, eval, evalCoeffs]

@[simp] private theorem point_re (x y : Coordinate) :
    (point x y).re = x := rfl

@[simp] private theorem point_im (x y : Coordinate) :
    (point x y).im = y := rfl

/-- The exact vertical-line resultant of `Z² - parameter`, written in a
form whose nonzeroness is directly decidable at rational box sides. -/
def verticalDeterminant (parameter : Gaussian) (x : Coordinate) : Coordinate :=
  4 * x ^ 2 * (x ^ 2 - parameter.re) - parameter.im ^ 2

/-- A displayed nonzero quadratic vertical resultant gives an explicit
Bézout certificate for the real and imaginary path polynomials. -/
def verticalCoprime (parameter : Gaussian) (x : Coordinate)
    (determinantNonzero : verticalDeterminant parameter x ≠ 0) :
    RFAP.PathClearance.CoprimeCertificate
      (pathReal (rootPolynomial parameter) (verticalBase x) verticalDirection)
      (pathImag (rootPolynomial parameter) (verticalBase x) verticalDirection) where
  left := constant (4 * x ^ 2 / verticalDeterminant parameter x)
  right := linearPolynomial
    (2 * x / verticalDeterminant parameter x)
    (parameter.im / verticalDeterminant parameter x)
  identity := by
    intro y
    simp only [eval_constant, eval_linearPolynomial, eval_pathReal,
      eval_pathImag, rootPolynomial, CCL.PowerMonodromy.polynomial_eval,
      CCL.Riemann.SquareRootSheets.degreeTwo_value, pow_two, line_vertical,
      sub_re, sub_im, mul_re, mul_im, point_re, point_im]
    rw [RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ExplicitField.div_eq_mul_inv]
    calc
      1 = (verticalDeterminant parameter x)⁻¹ *
          verticalDeterminant parameter x :=
        (RFAP.ConstructiveFraction.inv_mul_cancel _ determinantNonzero).symm
      _ = _ := by
        dsimp only [verticalDeterminant]
        ring1

/-- The exact horizontal-line resultant of `Z² - parameter`. -/
def horizontalDeterminant
    (parameter : Gaussian) (y : Coordinate) : Coordinate :=
  parameter.im ^ 2 - 4 * y ^ 2 * (y ^ 2 + parameter.re)

/-- A displayed nonzero quadratic horizontal resultant gives an explicit
Bézout certificate for the real and imaginary path polynomials. -/
def horizontalCoprime (parameter : Gaussian) (y : Coordinate)
    (determinantNonzero : horizontalDeterminant parameter y ≠ 0) :
    RFAP.PathClearance.CoprimeCertificate
      (pathReal (rootPolynomial parameter) (horizontalBase y) horizontalDirection)
      (pathImag (rootPolynomial parameter) (horizontalBase y) horizontalDirection) where
  left := constant (4 * y ^ 2 / horizontalDeterminant parameter y)
  right := linearPolynomial
    (-(2 * y) / horizontalDeterminant parameter y)
    (-parameter.im / horizontalDeterminant parameter y)
  identity := by
    intro x
    simp only [eval_constant, eval_linearPolynomial, eval_pathReal,
      eval_pathImag, rootPolynomial, CCL.PowerMonodromy.polynomial_eval,
      CCL.Riemann.SquareRootSheets.degreeTwo_value, pow_two, line_horizontal,
      sub_re, sub_im, mul_re, mul_im, point_re, point_im]
    rw [RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ExplicitField.div_eq_mul_inv]
    calc
      1 = (horizontalDeterminant parameter y)⁻¹ *
          horizontalDeterminant parameter y :=
        (RFAP.ConstructiveFraction.inv_mul_cancel _ determinantNonzero).symm
      _ = _ := by
        dsimp only [horizontalDeterminant]
        ring1

/-- Extend one already displayed quadratic winding-one state to a total
square-root owner.  This bypasses only global all-root isolation; every later
requested refinement still uses the same finite squarefree Newton process. -/
def ofState {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    {ambient : Box}
    (initial : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient) : Owner parameter where
  parameterNonzero := parameterNonzero
  ambient := ambient
  track := RFAP.ShrinkingTrack.ofInitial
    (by
      rw [CCL.PowerMonodromy.polynomial_degree]
      decide)
    (CCL.PowerMonodromy.squarefree parameterNonzero
      CCL.Riemann.SquareRootSheets.degreeTwo)
    (RFAP.AxisSafeCuts.separatedAxisEliminationCertificate
      (rootPolynomial parameter)
      (CCL.PowerMonodromy.polynomial_nonzero parameter
        CCL.Riemann.SquareRootSheets.degreeTwo)
      (by
        unfold rootPolynomial
        rw [CCL.PowerMonodromy.polynomial_degree]
        exact CCL.Riemann.SquareRootSheets.degreeTwo.positive))
    initial

/-- Construct a total quadratic owner from one rational box.  The four
displayed determinant checks supply its side clearances, and the winding
equation identifies the selected occurrence. -/
def ofBox {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (box : Box) (proper : box.Proper)
    (leftNonzero : verticalDeterminant parameter box.xLower ≠ 0)
    (rightNonzero : verticalDeterminant parameter box.xUpper ≠ 0)
    (bottomNonzero : horizontalDeterminant parameter box.yLower ≠ 0)
    (topNonzero : horizontalDeterminant parameter box.yUpper ≠ 0)
    (windingFour : quadrupledBoxWinding (rootPolynomial parameter) box = 4) :
    Owner parameter := by
  let left := RFAP.BoxClearance.verticalOfCoprime
    (rootPolynomial parameter) box box.xLower
    (verticalCoprime parameter box.xLower leftNonzero)
  let right := RFAP.BoxClearance.verticalOfCoprime
    (rootPolynomial parameter) box box.xUpper
    (verticalCoprime parameter box.xUpper rightNonzero)
  let bottom := RFAP.BoxClearance.horizontalOfCoprime
    (rootPolynomial parameter) box box.yLower
    (horizontalCoprime parameter box.yLower bottomNonzero)
  let top := RFAP.BoxClearance.horizontalOfCoprime
    (rootPolynomial parameter) box box.yUpper
    (horizontalCoprime parameter box.yUpper topNonzero)
  let clearance := RFAP.BoxClearance.boundaryOfLines left right bottom top
  exact ofState parameterNonzero
    { box := box
      refinesAmbient := RFAP.Boxes.Box.refines_refl box
      proper := proper
      clearance := clearance
      rawWindingFour := windingFour
      ambientLeftClearance := left
      ambientRightClearance := right
      ambientBottomClearance := bottom
      ambientTopClearance := top }

def localOwner {parameter : Gaussian} (owner : Owner parameter) :
    CCL.ProgressivePolynomialRoots.LocalOwner
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) where
  box := owner.track.initial.box
  proper := owner.track.initial.proper
  clearance := owner.track.initial.clearance
  rawWindingFour := owner.track.initial.rawWindingFour

/-- One of the two canonical initial owners. -/
def independent {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) : Owner parameter where
  parameterNonzero := parameterNonzero
  ambient := RFAP.GlobalWinding.largeSquareBox
    (CCL.PowerMonodromy.polynomial parameter
      CCL.Riemann.SquareRootSheets.degreeTwo)
  track := CCL.Riemann.SquareRootSheets.track parameterNonzero sheet

/-- Advance the owner across one certified small parameter move. -/
def advance {source target : Gaussian} (owner : Owner source)
    (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound) : Owner target := by
  exact
    { parameterNonzero := targetNonzero
      ambient := CCL.Riemann.SquareRootContinuation.commonAmbient
        owner.track.initial target
      track := CCL.Riemann.SquareRootContinuation.continuedTrack
        targetNonzero owner.track.initial small }

/-- Restart an owner at one explicitly computed state of its own shrinking
track.  The operation retains the same finite occurrence while replacing the
initial box by a quantitatively smaller one. -/
def refineAt {parameter : Gaussian} (owner : Owner parameter)
    (index : Nat) : Owner parameter where
  parameterNonzero := owner.parameterNonzero
  ambient := owner.ambient
  track :=
    { initial := CCL.Riemann.CoherentRoot.state owner.track index
      refine := owner.track.refine
      nested := owner.track.nested
      strict := owner.track.strict
      accurate := owner.track.accurate }

@[simp] theorem refineAt_initial {parameter : Gaussian}
    (owner : Owner parameter) (index : Nat) :
    (refineAt owner index).track.initial =
      CCL.Riemann.CoherentRoot.state owner.track index := rfl

theorem refineAt_initial_refines {parameter : Gaussian}
    (owner : Owner parameter) (index : Nat) :
    (refineAt owner index).track.initial.box.Refines
      owner.track.initial.box :=
  CCL.Riemann.CoherentRoot.state_refines_of_le owner.track
    (Nat.zero_le index)

/-- First positive state whose squared diagonal is below the requested
positive rational target. -/
def preparationIndex {parameter : Gaussian} (owner : Owner parameter)
    (target : RFAP.ConstructiveFraction.Rational) (positive : 0 < target) : Nat :=
  (CCL.Riemann.CoherentRoot.approximation owner.track).refineIndex
    1 target positive

theorem preparationIndex_positive {parameter : Gaussian}
    (owner : Owner parameter)
    (target : RFAP.ConstructiveFraction.Rational) (positive : 0 < target) :
    0 < preparationIndex owner target positive := by
  exact (Nat.zero_lt_succ 0).trans_le
    ((CCL.Riemann.CoherentRoot.approximation owner.track).refineIndex_ge
      1 target positive)

/-- Executably prepare an owner to a requested squared diameter before a
continuation move. -/
def prepare {parameter : Gaussian} (owner : Owner parameter)
    (target : RFAP.ConstructiveFraction.Rational) (positive : 0 < target) :
    Owner parameter :=
  refineAt owner (preparationIndex owner target positive)

/-- The exact squarefree derivative separation on the currently displayed
owner box. -/
def quantitativePreparationSeparation {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0) :=
  RFAP.DerivativeSeparation.ofSquarefree
    (CCL.PowerMonodromy.squarefree parameterNonzero
      CCL.Riemann.SquareRootSheets.degreeTwo) owner.track.initial.box

/-- Exact coefficient majorants on the currently displayed owner box. -/
def quantitativePreparationMajorants {parameter : Gaussian}
    (owner : Owner parameter) :=
  RFAP.NewtonExtraction.exactExtractionMajorants (rootPolynomial parameter)
    owner.track.initial.box

/-- The positive rational clearance promised before quantitative preparation
is executed.  It is an explicit expression in the current box, its boundary
clearance, the squarefree Bézout separation, and the requested diameter. -/
def quantitativePreparedClearanceLower {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0)
    (target : RFAP.ConstructiveFraction.Rational) :
    RFAP.ConstructiveFraction.Rational :=
  RFAP.NewtonExtraction.predictedExtractionClearance
    (quantitativePreparationSeparation owner parameterNonzero)
    owner.track.initial.clearance
    (quantitativePreparationMajorants owner)
    (CCL.BoxedNameProcess.accuracyRadius target)

theorem quantitativePreparedClearanceLower_positive {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0)
    (target : RFAP.ConstructiveFraction.Rational) (positive : 0 < target) :
    0 < quantitativePreparedClearanceLower owner parameterNonzero target := by
  exact RFAP.NewtonExtraction.predictedExtractionClearance_pos
    (quantitativePreparationSeparation owner parameterNonzero)
    owner.track.initial.clearance (quantitativePreparationMajorants owner)
    owner.track.initial.proper
    (CCL.BoxedNameProcess.accuracyRadius_pos positive)

/-- The separated Newton extraction used by quantitative owner preparation.
Unlike the generic recursive track step, this output retains an explicit
coefficient-computed lower bound for its new boundary clearance. -/
def quantitativePreparationOutput {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0)
    (target : RFAP.ConstructiveFraction.Rational) (positive : 0 < target) :=
  let p := rootPolynomial parameter
  let current := owner.track.initial.raw
  let separation := quantitativePreparationSeparation owner parameterNonzero
  let majorants := quantitativePreparationMajorants owner
  RFAP.NewtonExtraction.extractSeparatedMajorized
    (by
      rw [CCL.PowerMonodromy.polynomial_degree]
      exact CCL.Riemann.SquareRootSheets.degreeTwo_atLeastTwo)
    current separation majorants
    (CCL.PowerMonodromy.isolationInput parameterNonzero
      CCL.Riemann.SquareRootSheets.degreeTwo
      CCL.Riemann.SquareRootSheets.degreeTwo_atLeastTwo).elimination
    (CCL.BoxedNameProcess.accuracyRadius_pos positive)

/-- Restart the quantitatively extracted square as its own finite ambient
region.  Boundary clearance itself supplies all four ambient-side
certificates, so no global-line choice is hidden in this restart. -/
def quantitativePreparedInitial {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0)
    (target : RFAP.ConstructiveFraction.Rational) (positive : 0 < target) :
    RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter)
      (quantitativePreparationOutput owner parameterNonzero target
        positive).core.box := by
  let output := quantitativePreparationOutput owner parameterNonzero target
    positive
  let clearance := output.clearance
  let initial : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) output.core.box :=
    { box := output.core.box
      refinesAmbient := RFAP.Boxes.Box.refines_refl output.core.box
      proper := output.core.proper
      clearance := clearance
      rawWindingFour := output.core.rawWindingFour
      ambientLeftClearance := RFAP.BoxClearance.leftOfBoundary clearance
      ambientRightClearance := RFAP.BoxClearance.rightOfBoundary clearance
      ambientBottomClearance := RFAP.BoxClearance.bottomOfBoundary clearance
      ambientTopClearance := RFAP.BoxClearance.topOfBoundary clearance }
  exact initial

/-- Prepare a square-root owner to a requested squared diameter while
retaining the explicit predicted Newton-clearance lower bound.  The new
owner remains fully executable: subsequent refinements use the ordinary
finite Newton-band track inside the extracted square. -/
def quantitativePrepare {parameter : Gaussian} (owner : Owner parameter)
    (parameterNonzero : parameter ≠ 0)
    (target : RFAP.ConstructiveFraction.Rational) (positive : 0 < target) :
    Owner parameter := by
  let output := quantitativePreparationOutput owner parameterNonzero target
    positive
  let initial := quantitativePreparedInitial owner parameterNonzero target
    positive
  exact
    { parameterNonzero := parameterNonzero
      ambient := output.core.box
      track := RFAP.ShrinkingTrack.ofInitial
        (by
          rw [CCL.PowerMonodromy.polynomial_degree]
          exact CCL.Riemann.SquareRootSheets.degreeTwo_atLeastTwo)
        (CCL.PowerMonodromy.squarefree parameterNonzero
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (CCL.PowerMonodromy.isolationInput parameterNonzero
          CCL.Riemann.SquareRootSheets.degreeTwo
          CCL.Riemann.SquareRootSheets.degreeTwo_atLeastTwo).elimination
        initial }

/-- Quantitative preparation is strictly nested in the supplied owner. -/
theorem quantitativePrepare_initial_strict {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0)
    (target : RFAP.ConstructiveFraction.Rational) (positive : 0 < target) :
    (quantitativePrepare owner parameterNonzero target positive).track.initial.box.StrictInterior
      owner.track.initial.box := by
  exact (quantitativePreparationOutput owner parameterNonzero target
    positive).core.strictCurrent

/-- The prepared box meets the requested squared-diameter target. -/
theorem quantitativePrepare_diagonal_lt {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0)
    (target : RFAP.ConstructiveFraction.Rational) (positive : 0 < target) :
    (quantitativePrepare owner parameterNonzero target
      positive).track.initial.box.diagonalSq < target := by
  exact (quantitativePreparationOutput owner parameterNonzero target
    positive).core.diagonalSq_le.trans_lt
      (CCL.BoxedNameProcess.accuracyRadius_sq_lt positive)

/-- The a-priori rational prediction is a lower bound for the actual boundary
clearance carried by the quantitatively prepared owner. -/
theorem quantitativePreparedClearanceLower_le {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0)
    (target : RFAP.ConstructiveFraction.Rational) (positive : 0 < target) :
    quantitativePreparedClearanceLower owner parameterNonzero target ≤
      (quantitativePrepare owner parameterNonzero target
        positive).track.initial.clearance.bound := by
  exact (quantitativePreparationOutput owner parameterNonzero target
    positive).predicted_clearance_le

attribute [irreducible] quantitativePrepare

theorem prepare_diagonal_lt {parameter : Gaussian}
    (owner : Owner parameter)
    (target : RFAP.ConstructiveFraction.Rational) (positive : 0 < target) :
    (prepare owner target positive).track.initial.box.diagonalSq < target := by
  let approximation := CCL.Riemann.CoherentRoot.approximation owner.track
  let index := preparationIndex owner target positive
  calc
    (prepare owner target positive).track.initial.box.diagonalSq <=
        CCL.FiniteGeometric.quarterRadius
          (CCL.Riemann.CoherentRoot.scale owner.track) index :=
      CCL.Riemann.CoherentRoot.state_diagonal_le owner.track index
    _ < target := approximation.refineIndex_accurate 1 target positive

theorem prepare_initial_refines {parameter : Gaussian}
    (owner : Owner parameter)
    (target : RFAP.ConstructiveFraction.Rational) (positive : 0 < target) :
    (prepare owner target positive).track.initial.box.Refines
      owner.track.initial.box :=
  refineAt_initial_refines owner _

/-- A continued owner exposes a division-ready CCL value and an operational
square equation, just like an independently isolated owner. -/
def certificate {parameter : Gaussian} (owner : Owner parameter)
    (parameterNonzero : parameter ≠ 0) :
    CCL.Riemann.CertifiedSquareRoot.Certificate parameter :=
  CCL.Riemann.CertifiedSquareRoot.certificate parameterNonzero owner.track

/-- Every finite candidate of the division-ready root name remains in the
owner's initial winding-one box, including candidates reached after arbitrary
later CCL refinements. -/
theorem certificate_candidate_in_initial_box {parameter : Gaussian}
    (owner : Owner parameter) (parameterNonzero : parameter ≠ 0)
    (state : (owner.certificate parameterNonzero).value.name.process.State)
    {candidate : Gaussian}
    (possible : (owner.certificate parameterNonzero).value.name.process.Possible
      state candidate) :
    owner.track.initial.box.Contains candidate := by
  change
    (CCL.Riemann.CertifiedSquareRoot.approximation owner.track).Possible
      state.source candidate at possible
  rcases possible with ⟨later, order, rfl⟩
  simp only [CCL.Riemann.CertifiedSquareRoot.approximation,
    CCL.Riemann.SquareRootSheets.tail_sample,
    CCL.Riemann.CoherentRoot.approximation_sample]
  exact (CCL.Riemann.CoherentRoot.state_refines_of_le owner.track
    (Nat.zero_le _)).contains
      (CCL.Riemann.CoherentRoot.state owner.track
        (max (CCL.Riemann.CertifiedSquareRoot.baseIndex owner.track)
          later)).box.contains_anchor

/-- The fresh target owner remains inside the source occurrence, which is the
finite same-sheet witness for this continuation step. -/
theorem advance_initial_box_refines {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound) :
    (advance owner targetNonzero small).track.initial.box.Refines
      owner.track.initial.box :=
  CCL.Riemann.SquareRootContinuation.continuedTrack_initial_refines_source
    targetNonzero owner.track.initial small

/-- The finite Rouché construction computes a fresh positive boundary
clearance for the transported owner. -/
theorem advance_clearance_positive {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound) :
    0 < (advance owner targetNonzero small).track.initial.clearance.bound :=
  (advance owner targetNonzero small).track.initial.clearance.positive

@[simp] theorem independent_root_eq {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) :
    (certificate (independent parameterNonzero sheet) parameterNonzero).value =
      (CCL.Riemann.SquareRootSheets.sheet parameterNonzero sheet).value :=
  rfl

end Owner

/-- A parameter packaged with its executable owner.  Packing the dependent
ambient and polynomial indices keeps finite chain recursion lightweight. -/
structure PackedOwner where
  parameter : Gaussian
  owner : Owner parameter

namespace PackedOwner

def independent {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) : PackedOwner :=
  ⟨parameter, Owner.independent parameterNonzero sheet⟩

def advance (current : PackedOwner) (target : Gaussian)
    (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq
      (current.parameter - target) <
        current.owner.track.initial.clearance.bound) : PackedOwner :=
  ⟨target, current.owner.advance targetNonzero small⟩

end PackedOwner

/-- A finite sequence of Rouché-certified small moves.  Each recursive tail
starts definitionally at the owner computed by the preceding move. -/
inductive Chain : PackedOwner → Type
  | nil (owner : PackedOwner) : Chain owner
  | step (owner : PackedOwner) (target : Gaussian)
      (targetNonzero : target ≠ 0)
      (small : RFAP.ConstructiveGaussian.Gaussian.normSq
        (owner.parameter - target) <
          owner.owner.track.initial.clearance.bound)
      (remaining : Chain
        (owner.advance target targetNonzero small)) :
      Chain owner

namespace Chain

/-- Number of actual parameter moves in the finite certificate. -/
def length {initial : PackedOwner} : Chain initial → Nat
  | .nil _ => 0
  | .step _ _ _ _ remaining => remaining.length + 1

/-- The final packed owner computed by the chain. -/
def endpoint {initial : PackedOwner} : Chain initial → PackedOwner
  | .nil owner => owner
  | .step _ _ _ _ remaining => remaining.endpoint

/-- Displayed radicands visited by the chain, including both endpoints. -/
def parameters {initial : PackedOwner} : Chain initial → List Gaussian
  | .nil owner => [owner.parameter]
  | .step owner _ _ _ remaining =>
      owner.parameter :: remaining.parameters

@[simp] theorem parameters_length {initial : PackedOwner}
    (chain : Chain initial) :
    chain.parameters.length = chain.length + 1 := by
  induction chain with
  | nil => rfl
  | step owner target targetNonzero small remaining inductionHypothesis =>
      simp only [parameters, List.length_cons, length, inductionHypothesis]

/-- Nonvanishing propagates through every explicitly certified move. -/
theorem endpointNonzero {initial : PackedOwner} (chain : Chain initial)
    (initialNonzero : initial.parameter ≠ 0) :
    chain.endpoint.parameter ≠ 0 :=
  match chain with
  | .nil _ => initialNonzero
  | .step _ _ targetNonzero _ remaining =>
      remaining.endpointNonzero targetNonzero

/-- The one-step chain generated by a single displayed Rouché inequality. -/
def single (owner : PackedOwner) (target : Gaussian)
    (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq
      (owner.parameter - target) <
        owner.owner.track.initial.clearance.bound) : Chain owner :=
  .step owner target targetNonzero small (.nil _)

@[simp] theorem length_single (owner : PackedOwner) (target : Gaussian)
    (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq
      (owner.parameter - target) <
        owner.owner.track.initial.clearance.bound) :
    (single owner target targetNonzero small).length = 1 := rfl

@[simp] theorem endpoint_single (owner : PackedOwner) (target : Gaussian)
    (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq
      (owner.parameter - target) <
        owner.owner.track.initial.clearance.bound) :
    (single owner target targetNonzero small).endpoint =
      owner.advance target targetNonzero small := rfl

end Chain

/-- A finite continuation rooted at one explicit initial sheet index.  The
sheet label is assigned only once; all later values inherit it through the
Rouché chain rather than consulting a fresh isolation ordering. -/
structure SeededChain (source : Gaussian) (sourceNonzero : source ≠ 0) where
  sheet : Fin 2
  continuation : Chain
    (PackedOwner.independent sourceNonzero sheet)

namespace SeededChain

def initial (source : Gaussian) (sourceNonzero : source ≠ 0)
    (sheet : Fin 2) : SeededChain source sourceNonzero where
  sheet := sheet
  continuation := .nil (PackedOwner.independent sourceNonzero sheet)

def endpoint {source : Gaussian} {sourceNonzero : source ≠ 0}
    (chain : SeededChain source sourceNonzero) : PackedOwner :=
  chain.continuation.endpoint

@[simp] theorem initial_endpoint_parameter (source : Gaussian)
    (sourceNonzero : source ≠ 0) (sheet : Fin 2) :
    (initial source sourceNonzero sheet).endpoint.parameter = source := rfl

def rootCertificate {source : Gaussian} {sourceNonzero : source ≠ 0}
    (chain : SeededChain source sourceNonzero) :
    CCL.Riemann.CertifiedSquareRoot.Certificate chain.endpoint.parameter :=
  chain.endpoint.owner.certificate
    (chain.continuation.endpointNonzero sourceNonzero)

/-- Use the endpoint of a same-owner chain as the algebraic sheet over a
rational curve point. -/
def algebraicSheetValue {genus : Nat}
    (curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus)
    (point source : Gaussian) (sourceNonzero : source ≠ 0)
    (chain : SeededChain source sourceNonzero)
    (endpoint_eq : chain.endpoint.parameter = curve.polynomial.eval point) :
    CCL.Riemann.AlgebraicDifferentials.AlgebraicSheetValue curve point := by
  let root := chain.rootCertificate
  have rootSquare : CCL.OperationalEquivalence.NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul root.value root.value).name
      (CCL.ProgressiveTransducer.Named.exact
        (curve.polynomial.eval point)) := by
    rw [← endpoint_eq]
    exact root.square
  exact
    { value := root.value
      apart := root.apart
      sheet := chain.sheet
      curveEquation :=
        CCL.OperationalEquivalence.NamedEquivalent.trans rootSquare
          (CCL.OperationalEquivalence.NamedEquivalent.symm
            (CCL.ProjectiveRationalEvaluation.polynomialEval_exact
              curve.polynomial point)) }

end SeededChain

end CCL.Riemann.SquareRootContinuationChain
