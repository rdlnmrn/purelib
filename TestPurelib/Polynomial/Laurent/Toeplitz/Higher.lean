module

public import Purelib.Polynomial.Laurent.Toeplitz
import TestPurelib.Polynomial.Laurent.Toeplitz
import Purelib.LinearAlgebra.Matrix.NormalForm.Coordinates
public import Purelib.Polynomial.Power.Gaussian
public import Purelib.RootIsolation.Power.Isolation
import Purelib.RootIsolation.FTA.Squarefree.Build
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Cofactor
import Purelib.RootIsolation.Multiplicity.Observation.Build
import Purelib.Data.Rat.Fraction.Field.Finite
import Purelib.System.IO

/-!
# Original irrational observations in the public scalar index construction

The same original squarefree quadratic input supplies a complete saved
isolation, radial inventory and center-product argument. Finite preprocessing
identifies its original focused context before these retained caches enter
the public comparison for `z-2*z^-1`.
-/

namespace TestPurelib.Polynomial.Laurent.Toeplitz.Higher

open Purelib
open Data.Gaussian.Basic (Canonical)
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Dense.Gaussian
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open RootIsolation.FTA.Squarefree
open RootIsolation.Multiplicity.Circle
open Polynomial.Clearance.Circle (Certificate FactorMargin)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput
  (FactorObservation PositiveFamily)
open Data.List (DependentProduct)
open RationalFunctions.Curve.Canonical.Circle
open RootIsolation.Multiplicity.Circle renaming Comparison → PolynomialComparison
open RootIsolation.Multiplicity.Side.Basic (SideResult)
open Polynomial.Dense.Basic (DensePolynomial)
open Polynomial.Laurent.Basic (LaurentPolynomial)
open Polynomial.Laurent.Normalization (Normalized)
open LinearAlgebra.Matrix
open Data renaming Vector → Vec
open Data.Vector.Basic

/-- The same original quadratic power-family degree used by the saved isolation. -/
public abbrev degree : Data.Nat.Positive.RootDegree := ⟨2, by decide⟩

/-- The same original descending quadratic table `z²-2`. -/
public abbrev polynomial : CoefficientPolynomial := Polynomial.Power.Gaussian.rootPolynomial 2 degree

/-- The complete original power-family squarefree input, including its canonical Euclidean certificate. -/
public abbrev isolationInput : Input polynomial :=
  RootIsolation.Power.Isolation.isolationInput (show (2 : Canonical) ≠ 0 by decide) degree (by decide)

/-- The original quadratic coefficient table is normalized and nonzero. -/
private theorem source_normalized : polynomial.normalize = polynomial := by decide +kernel

/-- The original nonzero quadratic has positive represented degree. -/
private theorem source_nonzero : polynomial.isZero = false := by decide +kernel

/-- The canonical side input retains the original preprocessing and coprimality to one.

The exposed original cache fixes the dependent product's runtime layout for
clients of the retained quadratic geometry.
-/
@[expose] public def sideInput : PositiveSideInput polynomial (DensePolynomial.constant 1) :=
  let preprocessing : Squarefree.Decomposition.Compute.PositivePreprocessing polynomial :=
    match Squarefree.Decomposition.Compute.preprocess polynomial with
    | .positive positive => positive
    | .zero zero => False.elim (Bool.noConfusion
        ((show polynomial.isZero = false by decide +kernel).symm.trans zero))
    | .constant _ degreeZero => False.elim (by
        have impossible : (2 : Nat) = 0 := degreeZero
        cases impossible)
  { sourceNormalized := by decide +kernel, preprocessing := preprocessing
    oppositeNonzero := by decide +kernel
    sourceOppositeCoprime := Coprime.Operations.CoprimeCertificate.constantRight (by decide +kernel) }

/-- The same original multiplicity preprocessing has exactly one focused context. -/
private theorem context_count : sideInput.contexts.length = 1 := by decide +kernel

/-- The original singleton occurrence is retained with its own checked context bound. -/
private def context := sideInput.contexts.get ⟨0, context_count.symm ▸ (by decide)⟩

/-- The original focused polynomial is the complete quadratic, with no replacement coefficient owner. -/
private theorem focused_polynomial : context.focus.part.polynomial = polynomial := by decide +kernel

/-- The original focused multiplicity is one. -/
private theorem focused_multiplicity : context.focus.multiplicity = 1 := by decide +kernel

/-- The focused part retains the identical original canonical Euclidean squarefree certificate. -/
private theorem focused_squarefree :
    (show Squarefree.Basic.SquarefreeCertificate polynomial from
      focused_polynomial ▸ context.focus.part.squarefree) = isolationInput.squarefree :=
  Coprime.Basic.CoprimeCertificate.eq_of_inputs _ _

/-- The complete focused higher input is the same original saved power-family input.

This equality includes the original normalized part and executable Euclidean
certificate. It does not compare or evaluate numerical isolation outputs.
-/
private theorem focused_input :
    (show Input polynomial from focused_polynomial ▸
      ({ squarefree := context.focus.part.squarefree
         degreeAtLeastTwo := show 2 ≤ context.focus.part.polynomial.natDegree from
           focused_polynomial.symm ▸ (by decide) } : Input context.focus.part.polynomial)) = isolationInput := by
  exact Input.eq_of_polynomial _ _

/-- The same original focused part has higher represented degree. -/
private theorem focused_higher : 2 ≤ context.focus.part.polynomial.natDegree :=
  focused_polynomial.symm ▸ (by decide)

/-- Read the complete saved box result under the equal original focused polynomial. -/
private def focusedBoxes (prepared : Input.Prepared isolationInput) :
    BoxResult context.focus.part.polynomial :=
  focused_polynomial.symm ▸ Build.BoxFTA.ofPrepared prepared

/-- The same saved boxes are the complete original higher focused constructor result. -/
private theorem focusedBoxes_eq (prepared : Input.Prepared isolationInput) :
    focusedBoxes prepared = Build.BoxFTA.prove
      { squarefree := context.focus.part.squarefree, degreeAtLeastTwo := focused_higher } :=
  (congrArg (fun boxes : BoxResult polynomial => focused_polynomial.symm ▸ boxes)
    (Build.BoxFTA.ofPrepared_eq_prove prepared)).trans
      ((Build.BoxFTA.prove_transport focused_polynomial.symm isolationInput).trans
        (congrArg Build.BoxFTA.prove (Input.eq_of_polynomial _ _)))

/-- A complete same-source canonical box equation transports to the original focused input. -/
private theorem transportedBoxes_eq (boxes : BoxResult polynomial)
    (boxesEq : boxes = Build.BoxFTA.prove isolationInput) :
    (show BoxResult context.focus.part.polynomial from focused_polynomial.symm ▸ boxes) =
      Build.BoxFTA.prove {squarefree := context.focus.part.squarefree, degreeAtLeastTwo := focused_higher} :=
  (congrArg (fun boxes : BoxResult polynomial => focused_polynomial.symm ▸ boxes) boxesEq).trans
    ((Build.BoxFTA.prove_transport focused_polynomial.symm isolationInput).trans
      (congrArg Build.BoxFTA.prove (Input.eq_of_polynomial _ _)))

/-- The original higher observation stores the same complete saved boxes. -/
private def observation (boxes : BoxResult context.focus.part.polynomial) :
    FactorObservation sideInput context := .higher boxes focused_higher

/-- A checked complete box cache returns the original canonical focused observation. -/
private theorem observation_eq (boxes : BoxResult context.focus.part.polynomial)
    (boxesEq : boxes = Build.BoxFTA.prove
      { squarefree := context.focus.part.squarefree, degreeAtLeastTwo := focused_higher }) :
    observation boxes = sideInput.observe context :=
  (congrArg (fun boxes => FactorObservation.higher boxes focused_higher) boxesEq).trans
    (sideInput.observe_higher context focused_higher).symm

/-- Every bounded original context occurrence is the same retained singleton occurrence. -/
private theorem context_index (index : Fin sideInput.contexts.length) :
    index = ⟨0, context_count.symm ▸ (by decide)⟩ := by
  apply Fin.ext
  change index.val = 0
  have bound : index.val < 1 := context_count ▸ index.isLt
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bound)

/-- Read the supplied original observation at the same singleton context without observing again. -/
private def observationAt (boxes : BoxResult context.focus.part.polynomial)
    (index : Fin sideInput.contexts.length) : FactorObservation sideInput (sideInput.contexts.get index) :=
  Eq.ndrec (motive := fun original : Fin sideInput.contexts.length =>
    FactorObservation sideInput (sideInput.contexts.get original)) (observation boxes) (context_index index).symm

/-- The same singleton observation cache restores every original context lookup. -/
private theorem observationAt_eq (boxes : BoxResult context.focus.part.polynomial)
    (boxesEq : boxes = Build.BoxFTA.prove
      { squarefree := context.focus.part.squarefree, degreeAtLeastTwo := focused_higher })
    (index : Fin sideInput.contexts.length) :
    observationAt boxes index = sideInput.observe (sideInput.contexts.get index) := by
  have same := context_index index
  cases same
  exact observation_eq boxes boxesEq

/-- Retain the singleton original family with its actual complete saved observation. -/
private def family (boxes : BoxResult context.focus.part.polynomial) : PositiveFamily sideInput :=
  sideInput.fromObservations (DependentProduct.ofFn sideInput.contexts (observationAt boxes))

/-- The retained original family equals the complete canonical family including all owner operations. -/
private theorem family_eq (boxes : BoxResult context.focus.part.polynomial)
    (boxesEq : boxes = Build.BoxFTA.prove
      { squarefree := context.focus.part.squarefree, degreeAtLeastTwo := focused_higher }) :
    family boxes = sideInput.buildFamily :=
  sideInput.fromObservations_eq_buildFamily _ (DependentProduct.ofFn_congr sideInput.contexts
    (observationAt boxes) (fun index => sideInput.observe (sideInput.contexts.get index))
      (observationAt_eq boxes boxesEq))

/-- The same original product spine returns its supplied saved observation. -/
private theorem family_observationAt (boxes : BoxResult context.focus.part.polynomial)
    (index : Fin sideInput.contexts.length) :
    (family boxes).observationAt index = observationAt boxes index :=
  DependentProduct.get_ofFn sideInput.contexts (observationAt boxes) index

/-- The original singleton context has the actual constant-one cofactor. -/
private theorem cofactor_polynomial :
    context.singleCofactor sideInput.preprocessing.decomposition =
      Polynomial.Dense.Basic.DensePolynomial.constant 1 := by decide +kernel

/-- The original Horner cache doubles the constant-one quadrance. -/
private theorem cofactor_bound :
    (Bounds.Box.denseHornerNormBounds
      (context.singleCofactor sideInput.preprocessing.decomposition)
      Geometry.Rational.Circle.boundingBox).value = 2 := by
  rewrite [cofactor_polynomial]
  decide +kernel

/-- Transfer the original source margin once through the same original focused factorization. -/
private def focusedMargin (clearance : Certificate polynomial) :=
  FactorMargin.prepare clearance (sideInput.focusFactorization context)

/-- The constant-one cofactor uses the exact singleton payment from its retained original Horner cache. -/
private theorem focusedMargin_majorant (clearance : Certificate polynomial) :
    (focusedMargin clearance).majorant = 1 := by
  rewrite [(focusedMargin clearance).majorant_eq, (focusedMargin clearance).bounds_eq, cofactor_polynomial]
  change max 1 ((Bounds.Box.denseHornerNormBounds
    (Polynomial.Dense.Basic.DensePolynomial.constant 1) Geometry.Rational.Circle.boundingBox).value / 2) = 1
  have value : (Bounds.Box.denseHornerNormBounds
      (Polynomial.Dense.Basic.DensePolynomial.constant 1) Geometry.Rational.Circle.boundingBox).value = 2 := by
    decide +kernel
  rewrite [value]
  change max (1 : Data.Rat.Fraction.Rational) 1 = 1
  exact Data.Rat.Fraction.Order.Basic.max_self 1

/-- The same singleton factorization preserves the complete original source certificate. -/
private theorem focusedMargin_certificate (clearance : Certificate polynomial) :
    (show Certificate polynomial from
      focused_polynomial ▸ (focusedMargin clearance).toCertificate) = clearance := by
  apply Certificate.eq_of_bound_eq
  apply (Certificate.transport_bound focused_polynomial (focusedMargin clearance).toCertificate).trans
  exact (focusedMargin clearance).bound_eq.trans
    ((congrArg (fun majorant => clearance.bound / majorant) (focusedMargin_majorant clearance)).trans
      (Data.Rat.Fraction.Field.Finite.rational_div_one clearance.bound))

/-- The same original locations and sufficient argument are retained together with complete producer equations. -/
private abbrev SavedGeometry {source : CoefficientPolynomial} (clearance : Certificate source)
    (boxes : BoxResult source) (positive : 0 < source.natDegree) :=
  Σ locations : {locations : HigherLocations clearance boxes //
      locations = HigherLocations.prepare clearance boxes positive},
    {argument : CenterProduct.Approximation locations.val //
      argument = CenterProduct.Approximation.prepare locations.val}

/-- Complete polynomial, certificate and box equalities transport the same retained dependent geometry pair. -/
private def geometryTransport {source target : CoefficientPolynomial} (equal : source = target)
    {sourceClearance : Certificate source} {targetClearance : Certificate target}
    (clearanceEq : (show Certificate source from equal.symm ▸ targetClearance) = sourceClearance)
    {sourceBoxes : BoxResult source} {targetBoxes : BoxResult target}
    (boxesEq : (show BoxResult source from equal.symm ▸ targetBoxes) = sourceBoxes)
    {sourcePositive : 0 < source.natDegree} {targetPositive : 0 < target.natDegree}
    (geometry : SavedGeometry sourceClearance sourceBoxes sourcePositive) :
    SavedGeometry targetClearance targetBoxes targetPositive := by
  cases equal
  cases clearanceEq
  cases boxesEq
  exact geometry

/-- Transporting an original value along an equality and back preserves that complete value. -/
private theorem transport_back {α : Sort*} {family : α → Sort*} {source target : α}
    (equal : source = target) (value : family source) :
    (show family source from equal.symm ▸ (show family target from equal ▸ value)) = value := by
  cases equal
  rfl

/-- Retain the same original focused row and its complete sufficient argument from the saved geometry pair. -/
private def locationRow (clearance : Certificate polynomial) (sourceBoxes : BoxResult polynomial)
    (sourceBoxesEq : sourceBoxes = Build.BoxFTA.prove isolationInput)
    (geometry : SavedGeometry clearance sourceBoxes isolationInput.degreePositive) :
    Σ factor : Factor clearance sideInput context
      ((family (focused_polynomial.symm ▸ sourceBoxes)).observationAt
        ⟨0, context_count.symm ▸ (by decide)⟩),
      {argument : factor.Argument // argument = Factor.Argument.prepare factor} :=
  let boxes : BoxResult context.focus.part.polynomial := focused_polynomial.symm ▸ sourceBoxes
  let retained := geometryTransport focused_polynomial.symm (focusedMargin_certificate clearance)
    (transport_back focused_polynomial.symm sourceBoxes) geometry
  let margin := focusedMargin clearance
  let observed := observation boxes
  have boxesEq := transportedBoxes_eq sourceBoxes sourceBoxesEq
  have observedEq : observed = (family boxes).observationAt
      ⟨0, context_count.symm ▸ (by decide)⟩ :=
    (observation_eq boxes boxesEq).trans
      (((family_observationAt boxes ⟨0, context_count.symm ▸ (by decide)⟩).trans
        (observationAt_eq boxes boxesEq ⟨0, context_count.symm ▸ (by decide)⟩)).symm)
  let factor := Factor.ofCaches clearance sideInput context _ observed observedEq margin rfl
    retained.1.val retained.1.property
  ⟨factor, retained.2⟩

/-- The same original retained row type at the sole original context occurrence. -/
private abbrev Row (clearance : Certificate polynomial) (boxes : BoxResult context.focus.part.polynomial) :=
  Factor clearance sideInput context
    ((family boxes).observationAt ⟨0, context_count.symm ▸ (by decide)⟩)

/-- Read a supplied original row at the same bounded singleton occurrence. -/
private def rowAt {clearance : Certificate polynomial} {boxes : BoxResult context.focus.part.polynomial}
    (row : Row clearance boxes) (index : Fin sideInput.contexts.length) :
    Factor clearance sideInput (sideInput.contexts.get index) ((family boxes).observationAt index) :=
  Eq.ndrec (motive := fun original : Fin sideInput.contexts.length =>
    Factor clearance sideInput (sideInput.contexts.get original) ((family boxes).observationAt original))
      row (context_index index).symm

/-- Store the same supplied original row spine without another radial constructor. -/
private def positiveInventory {clearance : Certificate polynomial} {boxes : BoxResult context.focus.part.polynomial}
    (row : Row clearance boxes) : PositiveInventory clearance sideInput (family boxes) :=
  let factors := DependentProduct.ofFn sideInput.contexts (rowAt row)
  PositiveInventory.ofFactors clearance sideInput (family boxes) factors
    (DependentProduct.ofFn_congr sideInput.contexts (rowAt row)
      (fun index => Factor.prepare clearance sideInput (sideInput.contexts.get index)
        ((family boxes).observationAt index)) (fun index => Factor.restore (rowAt row index)))

/-- The original stored factor lookup returns the same supplied row at its retained bounded occurrence. -/
private theorem positiveInventory_factorAt {clearance : Certificate polynomial}
    {boxes : BoxResult context.focus.part.polynomial} (row : Row clearance boxes)
    (index : Fin sideInput.contexts.length) : (positiveInventory row).factorAt index = rowAt row index :=
  DependentProduct.get_ofFn sideInput.contexts (rowAt row) index

/-- Transporting a complete dependent constructor equation preserves its original producer. -/
private theorem transport_producer {α : Sort*} {family : α → Sort*} (producer : (value : α) → family value)
    {source target : α} (equal : source = target) (value : family source) (valueEq : value = producer source) :
    Eq.ndrec (motive := family) value equal = producer target := by
  cases equal
  exact valueEq

/-- Read the same supplied sufficient argument at its original stored singleton row. -/
private def argumentAt {clearance : Certificate polynomial} {boxes : BoxResult context.focus.part.polynomial}
    {row : Row clearance boxes} (argument : row.Argument) (index : Fin sideInput.contexts.length) :
    ((positiveInventory row).factorAt index).Argument :=
  let original : (rowAt row index).Argument :=
    Eq.ndrec (motive := fun original : Fin sideInput.contexts.length => (rowAt row original).Argument)
      argument (context_index index).symm
  Eq.ndrec (motive := fun factor => factor.Argument) original (positiveInventory_factorAt row index).symm

/-- The supplied same-row argument retains its complete original canonical producer equation. -/
private theorem argumentAt_eq {clearance : Certificate polynomial} {boxes : BoxResult context.focus.part.polynomial}
    {row : Row clearance boxes} (argument : row.Argument)
    (argumentEq : argument = Factor.Argument.prepare row) (index : Fin sideInput.contexts.length) :
    argumentAt argument index = Factor.Argument.prepare ((positiveInventory row).factorAt index) := by
  apply transport_producer (fun factor => Factor.Argument.prepare factor)
  exact transport_producer (fun original : Fin sideInput.contexts.length =>
    Factor.Argument.prepare (rowAt row original)) (context_index index).symm argument argumentEq

/-- Store the same original sufficient argument spine without sampling or synthetic division again. -/
private def positiveArgument {clearance : Certificate polynomial} {boxes : BoxResult context.focus.part.polynomial}
    {row : Row clearance boxes} (argument : row.Argument) (argumentEq : argument = Factor.Argument.prepare row) :
    PositiveArgument (positiveInventory row) :=
  let factors := DependentProduct.ofFn sideInput.contexts (argumentAt argument)
  PositiveArgument.ofFactors (positiveInventory row) factors
    (DependentProduct.ofFn_congr sideInput.contexts (argumentAt argument)
      (fun index => Factor.Argument.prepare ((positiveInventory row).factorAt index))
      (argumentAt_eq argument argumentEq))

/-- The same retained original singleton family is exactly the automatic positive side. -/
private theorem side_eq (clearance : Certificate polynomial) (boxes : BoxResult context.focus.part.polynomial)
    (boxesEq : boxes = Build.BoxFTA.prove
      { squarefree := context.focus.part.squarefree, degreeAtLeastTwo := focused_higher }) :
    SideResult.positive sideInput (family boxes) =
      RootIsolation.Multiplicity.Side.Build.buildSide polynomial (DensePolynomial.constant 1)
        source_normalized clearance.nonzero
        (Polynomial.Dense.Leading.LeadingTerm.constant (by decide : (1 : Canonical) ≠ 0)).nonzero
        (Coprime.Operations.CoprimeCertificate.constantRight clearance.nonzero) := by
  rewrite [family_eq boxes boxesEq]
  rfl

/-- Assemble the original complete inventory from the same singleton family and retained radial row. -/
private def inventory {clearance : Certificate polynomial} {boxes : BoxResult context.focus.part.polynomial}
    (boxesEq : boxes = Build.BoxFTA.prove
      { squarefree := context.focus.part.squarefree, degreeAtLeastTwo := focused_higher })
    (row : Row clearance boxes) : Inventory clearance :=
  let locations := positiveInventory row
  Inventory.ofCaches clearance source_normalized (.positive sideInput (family boxes))
    (side_eq clearance boxes boxesEq) locations (PositiveInventory.restore locations)

/-- Use the original public polynomial comparison with the same complete restored geometry caches.

The input is the original prepared quadratic isolation. The same source
margin, radial refinements and sufficient center approximation are retained;
no numerical construction is invoked again.
-/
public def ofGeometry (prepared : Input.Prepared isolationInput) (paths : Boundary.Substitutions polynomial)
    (clearance : Boundary.Clearance paths) (margin : Polynomial.Clearance.Circle.Margin paths clearance)
    (marginEq : margin = Polynomial.Clearance.Circle.Margin.prepare paths clearance)
    (reading : Polynomial.Winding.Circle.Reading paths clearance)
    (readingEq : reading = Polynomial.Winding.Circle.Reading.prepare paths clearance)
    (locations : HigherLocations margin.toCertificate (Build.BoxFTA.ofPrepared prepared))
    (locationsEq : locations = HigherLocations.prepare margin.toCertificate (Build.BoxFTA.ofPrepared prepared)
      isolationInput.degreePositive)
    (approximation : CenterProduct.Approximation locations)
    (approximationEq : approximation = CenterProduct.Approximation.prepare locations) :
    PolynomialComparison paths clearance :=
  let sourceBoxes := Build.BoxFTA.ofPrepared prepared
  let sourceBoxesEq := Build.BoxFTA.ofPrepared_eq_prove prepared
  let geometry : SavedGeometry margin.toCertificate sourceBoxes isolationInput.degreePositive :=
    ⟨⟨locations, locationsEq⟩, ⟨approximation, approximationEq⟩⟩
  let retained := locationRow margin.toCertificate sourceBoxes sourceBoxesEq geometry
  let boxesEq := transportedBoxes_eq sourceBoxes sourceBoxesEq
  let roots := inventory boxesEq retained.1
  let argument := positiveArgument retained.2.val retained.2.property
  PolynomialComparison.ofCaches paths clearance source_normalized margin marginEq reading readingEq
    roots (Inventory.restore roots) argument (PositiveArgument.restore argument)

/-- The original Laurent source has the same quadratic numerator and one actual pole. -/
private def symbol : LaurentPolynomial := ⟨[⟨1, .nonnegative 1⟩, ⟨-2, .negative 0⟩]⟩

/-- Cache the original source normalization once; its value at one excludes the zero branch. -/
private def normalized : Normalized symbol :=
  match symbol.prepare with
  | .normalized result => result
  | .zero zero => False.elim ((show symbol.eval 1 ≠ 0 by decide +kernel) zero.boundary_contact)

/-- The actual minimal polynomialization is the same original saved quadratic table. -/
private theorem normalized_polynomial : normalized.polynomial = polynomial := by decide +kernel

/-- The actual minimal pole order is one. -/
private theorem normalized_pole : normalized.poleOrder = 1 := by decide +kernel

/-- Retain a comparison with its same original dependent boundary paths and clearance. -/
private abbrev PolynomialResult (source : CoefficientPolynomial) :=
  Σ paths : Boundary.Substitutions source, Σ clearance : Boundary.Clearance paths,
    PolynomialComparison paths clearance

/-- Inspect the actual complete quadratic companion and full Hermite reconstruction, including both outside modes. -/
private def fullBasis {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite} {clearance : Certificate source} {family : PositiveFamily input}
    {inventory : PositiveInventory clearance input family} {argument : PositiveArgument inventory} {rows : Nat}
    (retained : Roots.Recurrence argument rows) : IO Unit := do
  let embedding := Multiplicity.Roots.Stages.Images.coefficientMap retained.prepared.separation.prepared.stages
  let companion := retained.recurrence.companion
  if sourceCount : retained.prepared.mapped.natDegree = 2 then
    let first : Fin retained.prepared.mapped.natDegree := ⟨0, sourceCount.symm ▸ (by decide)⟩
    let second : Fin retained.prepared.mapped.natDegree := ⟨1, sourceCount.symm ▸ (by decide)⟩
    unless decide (companion.matrix first first = embedding 0) &&
        decide (companion.matrix first second = embedding 1) &&
        decide (companion.matrix second first = embedding 2) &&
        decide (companion.matrix second second = embedding 0) do
      throw (IO.userError "the public irrational ledger lost its actual full quadratic companion")
  else
    throw (IO.userError "the public irrational ledger lost its degree-two full source companion")
  if wordCount : retained.recurrence.fullWord.length = 2 then
    let initial : Vec retained.prepared.separation.Scalar retained.recurrence.fullWord.length :=
      wordCount.symm ▸ .cons (embedding 1) (.cons (embedding 0) .nil)
    let coefficients := retained.recurrence.basis.coordinates initial
    let values := Rectangular.apply (retained.recurrence.basis.horizon 5) coefficients
    let expected : Vec retained.prepared.separation.Scalar 5 :=
      .cons (embedding 1) (.cons (embedding 0) (.cons (embedding 2) (.cons (embedding 0)
        (.cons (embedding 4) .nil))))
    for index in List.ofFn (fun index : Fin 5 => index) do
      unless decide (values index = expected index) do
        throw (IO.userError "the public irrational full basis lost the independent five-value recurrence")
  else
    throw (IO.userError "the public irrational ledger replaced the full basis by its empty selected word")
  if rowCount : rows = 1 then
    let normal := retained.boundary.selected.result.normal
    if complementCount : rows - normal.rank = 1 then
      let row : Fin rows := ⟨0, rowCount.symm ▸ (by decide)⟩
      let coordinate : Fin (rows - normal.rank) := ⟨0, complementCount.symm ▸ (by decide)⟩
      unless decide (normal.complementBasis row coordinate = embedding 1) do
        throw (IO.userError "the same public irrational normal form lost its literal complement [1]")
    else
      throw (IO.userError "the public irrational boundary lost its one complementary coordinate")
  else
    throw (IO.userError "the shifted public irrational boundary lost its one startup row")

/-- Dispatch the same original side solely to inspect its retained full source recurrence. -/
private def sourceBasis {source opposite : CoefficientPolynomial} {clearance : Certificate source} (rows : Nat) :
    (side : SideResult source opposite) → (locations : SideLocations clearance side) →
      (argument : SideArgument side locations) → Recurrence.Side rows side locations argument → IO Unit
  | .constant _ _ _, _, _, _ => throw (IO.userError "the original irrational quadratic became constant")
  | .positive _ _, _, _, retained => fullBasis retained

/-- Complete the public shifted irrational Laurent index from the same retained original geometry comparison.

The original quotient phase procedure computes winding independently. The
actual recurrence ledger retains its complete two-mode source companion and
basis, and its empty selected boundary has one genuine complementary vector.
-/
public def run {paths : Boundary.Substitutions polynomial} {clearance : Boundary.Clearance paths}
    (original : PolynomialComparison paths clearance) : IO Unit := do
  System.IO.println "Public irrational Toeplitz: original complete geometry retained; preparing actual ledger."
  let source : PolynomialResult polynomial := ⟨paths, clearance, original⟩
  let transferred : PolynomialResult normalized.polynomial := normalized_polynomial.symm ▸ source
  let circle := Polynomial.Laurent.Circle.Comparison.ofPolynomial normalized transferred.1 transferred.2.1
    transferred.2.2 (PolynomialComparison.restore transferred.2.2)
  let result := Polynomial.Laurent.Toeplitz.Comparison.ofCircle circle
    (Polynomial.Laurent.Circle.Comparison.ofPolynomial_eq_prepare normalized transferred.1 transferred.2.1
      transferred.2.2 (PolynomialComparison.restore transferred.2.2))
  unless normalized.poleOrder == 1 && result.circle.polynomial.inventory.insideCount == 0 &&
      result.circle.polynomial.inventory.outsideCount == 2 && result.index == 1 &&
      result.circle.reading.winding == -1 do
    throw (IO.userError "the original public irrational Laurent pole, inventory or independent winding changed")
  TestPurelib.Polynomial.Laurent.Toeplitz.ledger normalized.poleOrder 0 0 1 1 false
    result.circle.polynomial.inventory.side result.circle.polynomial.inventory.locations
    result.circle.polynomial.argument result.recurrence
  sourceBasis normalized.poleOrder result.circle.polynomial.inventory.side
    result.circle.polynomial.inventory.locations result.circle.polynomial.argument result.recurrence
  System.IO.println "Public irrational Toeplitz: actual rank0, kernel0, complement1, index1, winding-1."

end TestPurelib.Polynomial.Laurent.Toeplitz.Higher
