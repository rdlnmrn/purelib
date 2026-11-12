module

public import Purelib.Polynomial.Laurent.Toeplitz
import Purelib.LinearAlgebra.Matrix.NormalForm.Coordinates
import Purelib.System.IO

/-!
# Actual scalar Laurent–Toeplitz recurrence coordinates

Each finite source constructs its original normalization, independent circle
winding and actual recurrence ledger once. The same boundary matrices and
normal-form coordinates check both monomial signs, empty selections, true
zero transients and a coupled repeated-root startup row.
-/

namespace TestPurelib.Polynomial.Laurent.Toeplitz

open Purelib
open Polynomial.Laurent.Basic (LaurentPolynomial)
open Polynomial.Laurent.Normalization (Normalized)
open Polynomial.Laurent.Toeplitz (Comparison)
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Clearance.Circle (Certificate)
open RootIsolation.Multiplicity.Side.Basic (SideResult)
open RootIsolation.Multiplicity.Circle
open RationalFunctions.Curve.Canonical.Circle
open LinearAlgebra.Matrix
open Data renaming Vector → Vec
open Data.Vector.Basic
open Data.Gaussian.Basic (Canonical)

/-- Every actual public result reads its index from the same retained recurrence normal form. -/
private theorem index_from_boundary {source : LaurentPolynomial} {normalized : Normalized source}
    {paths : Boundary.Substitutions normalized.polynomial} {clearance : Boundary.Clearance paths}
    (result : Comparison normalized paths clearance) :
    result.index = -result.circle.reading.winding := result.index_eq_neg_winding

/-- The same original normal-form kernel constructor vanishes under the actual original matrix. -/
private theorem original_kernel {K : Type*} [CommRing K] {rows columns : Nat}
    {matrix : Rectangular K rows columns} (normal : NormalForm matrix)
    (coordinates : Vec K (columns - normal.rank)) :
    Rectangular.apply matrix (normal.kernelVector coordinates) = vectorOfFn (fun _ => 0) :=
  normal.matrix_kernelVector coordinates

/-- Check the actual source action and both target coordinate blocks of one retained normal form. -/
private def coordinates {K : Type*} [CommRing K] [DecidableEq K] {rows columns : Nat}
    {matrix : Rectangular K rows columns} (normal : NormalForm matrix) (embedding : Canonical → K)
    (rank kernel complement : Nat) (defect : Int) : IO Unit := do
  unless normal.rank == rank && normal.kernelDimension == kernel &&
      normal.cokernelDimension == complement && normal.defect == defect do
    throw (IO.userError "the actual Laurent recurrence normal-form dimensions changed")
  let free := vectorOfFn fun index : Fin (columns - normal.rank) => embedding (index.val + 1)
  let kernelVector := normal.kernelVector free
  let action := Rectangular.apply matrix kernelVector
  let recovered := normal.kernelCoordinates kernelVector
  for index in List.ofFn (fun index : Fin rows => index) do
    unless decide (action index = 0) do
      throw (IO.userError "the retained original boundary does not annihilate its actual kernel vector")
  for index in List.ofFn (fun index : Fin (columns - normal.rank) => index) do
    unless decide (recovered index = free index) do
      throw (IO.userError "the original kernel coordinates did not recover their actual input")
  let target := vectorOfFn fun index : Fin rows => embedding (index.val + 2)
  let image := normal.imageCoordinates target
  let remainder := normal.cokernelCoordinates target
  let reconstructed := normal.reconstruct image remainder
  let imageVector := normal.imageVector image
  let complementVector := normal.complementVector remainder
  let originalImage := Rectangular.apply matrix (normal.imagePreimage image)
  for index in List.ofFn (fun index : Fin rows => index) do
    unless decide (reconstructed index = target index) &&
        decide (imageVector index + complementVector index = target index) &&
        decide (originalImage index = imageVector index) do
      throw (IO.userError "the actual image and complementary coordinates lost original target reconstruction")

/-- The original empty-column branch retains the literal independent target coordinate basis. -/
private def constant {source : CoefficientPolynomial} {rows : Nat}
    (retained : Polynomial.Recurrence.Boundary.Constant source rows)
    (rank kernel complement : Nat) (defect : Int) : IO Unit := do
  coordinates retained.normal id rank kernel complement defect
  for row in List.ofFn (fun index : Fin rows => index) do
    for column in List.ofFn (fun index : Fin rows => index) do
      let original : Fin (rows - retained.normal.rank) :=
        ⟨column.val, by rewrite [retained.rank_eq]; exact column.isLt⟩
      unless decide (retained.normal.complementBasis row original = if row = column then 1 else 0) do
        throw (IO.userError "the actual constant recurrence lost its original complementary coordinate vectors")

/-- Check the demanded coupled row and kernel through the same actual selected boundary coordinates. -/
private def coupled {source opposite : CoefficientPolynomial}
    {input : Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {clearance : Certificate source}
    {family : Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.PositiveFamily input}
    {inventory : PositiveInventory clearance input family} {argument : PositiveArgument inventory} {rows : Nat}
    (retained : Roots.Recurrence argument rows) : IO Unit := do
  let embedding := Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Images.coefficientMap
    retained.prepared.separation.prepared.stages
  if fullCount : retained.recurrence.fullWord.length = 3 then
    let values : Vec retained.prepared.separation.Scalar 5 :=
      .cons (embedding 4) (.cons (embedding (17 / 2)) (.cons (embedding (57 / 4))
        (.cons (embedding (205 / 8)) (.cons (embedding (785 / 16)) .nil))))
    let enough : retained.recurrence.fullWord.length ≤ 5 := fullCount.symm ▸ (by decide : 3 ≤ 5)
    let coefficients := retained.recurrence.basis.coordinates (Data.Vector.Split.take enough values)
    for column in List.ofFn (fun index : Fin retained.recurrence.fullWord.length => index) do
      let root := retained.prepared.bank.block (retained.recurrence.fullWord[column.val]'column.isLt)
      let order := retained.recurrence.basis.occurrences.orders column
      if root.point = embedding (1 / 2) then
        unless order < 2 && decide (coefficients column = embedding (if order = 0 then 1 else 2)) do
          throw (IO.userError "the complete original basis lost its independent repeated-root coefficients")
      else
        unless decide (root.point = embedding 2) && order == 0 && decide (coefficients column = embedding 3) do
          throw (IO.userError "the complete original basis lost its independent outside-root coefficient")
    let reconstructed := Rectangular.apply (retained.recurrence.basis.horizon 5) coefficients
    for index in List.ofFn (fun index : Fin 5 => index) do
      unless decide (reconstructed index = values index) do
        throw (IO.userError "the complete original basis failed the independent five-value coupled recurrence")
  else
    throw (IO.userError "the complete original cubic basis was replaced by a selected boundary basis")
  if rowCount : rows = 1 then
    if columnCount : retained.boundary.selected.selection.word.length = 2 then
      let row : Fin rows := ⟨0, rowCount.symm ▸ (by decide)⟩
      let first : Fin retained.boundary.selected.selection.word.length :=
        ⟨0, columnCount.symm ▸ (by decide)⟩
      let second : Fin retained.boundary.selected.selection.word.length :=
        ⟨1, columnCount.symm ▸ (by decide)⟩
      let normal := retained.boundary.selected.result.normal
      let matrix := retained.boundary.selected.result.boundary
      unless decide (matrix row first = embedding 1) && decide (matrix row second = embedding (-2)) do
        throw (IO.userError "the actual Laurent coupled startup row changed from [1,-2]")
      if freeCount : retained.boundary.selected.selection.word.length - normal.rank = 1 then
        let free : Vec retained.prepared.separation.Scalar
            (retained.boundary.selected.selection.word.length - normal.rank) :=
          freeCount.symm ▸ .cons (embedding 1) .nil
        let values := normal.kernelVector free
        unless decide (values first = embedding 1) && decide (values second = embedding (1 / 2)) &&
            decide (Rectangular.apply matrix values row = 0) do
          throw (IO.userError "the same original Laurent boundary lost its kernel [1,1/2]")
      else
        throw (IO.userError "the coupled original Laurent boundary lost its single free coordinate")
    else
      throw (IO.userError "the coupled original Laurent boundary lost its two selected modes")
  else
    throw (IO.userError "the coupled original Laurent boundary lost its one startup row")

/-- Dispatch the retained original side and recurrence together, without reconstructing either parent. -/
public def ledger {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    (rows rank kernel complement : Nat) (defect : Int) (checkCoupled : Bool) :
    (side : SideResult source opposite) → (locations : SideLocations clearance side) →
      (argument : SideArgument side locations) → Recurrence.Side rows side locations argument → IO Unit
  | .constant _ _ _, _, _, retained => do
      if checkCoupled then throw (IO.userError "the coupled Laurent source unexpectedly became constant")
      constant retained.down rank kernel complement defect
  | .positive _ _, _, _, retained => do
      let embedding := Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Images.coefficientMap
        retained.prepared.separation.prepared.stages
      coordinates retained.boundary.selected.result.normal embedding rank kernel complement defect
      if checkCoupled then coupled retained

/-- Construct the complete public comparison once and inspect its same original recurrence branch. -/
private def check (label : String) (source : LaurentPolynomial) (depth pole inside rank kernel complement : Nat)
    (index : Int) (checkCoupled : Bool := false) : IO Unit := do
  System.IO.println s!"Toeplitz {label}: preparing original normalization and whole-circle certificate."
  match source.prepare with
  | .zero _ => throw (IO.userError "a nonzero Toeplitz fixture returned the zero-symbol obstruction")
  | .normalized normalized =>
      let boundary := Boundary.prepare normalized.polynomial depth
      match boundary.2 with
      | .clear clearance =>
          System.IO.println s!"Toeplitz {label}: preparing one actual public comparison."
          let result := Comparison.prepare normalized boundary.1.paths clearance
          unless normalized.poleOrder == pole &&
              result.circle.polynomial.inventory.insideCount == inside &&
              result.index == index && result.circle.reading.winding == -index do
            throw (IO.userError
              "the public Laurent recurrence index lost its original pole, multiplicity or winding sign")
          ledger normalized.poleOrder rank kernel complement index checkCoupled
            result.circle.polynomial.inventory.side result.circle.polynomial.inventory.locations
            result.circle.polynomial.argument result.recurrence
          System.IO.println s!"Toeplitz {label}: actual rank{rank}, kernel{kernel}, \
            complement{complement}, index{index}."
      | .contact _ _ _ => throw (IO.userError "a nonvanishing Toeplitz fixture met the unit circle")
      | .inconclusive _ _ _ _ _ => throw (IO.userError "a Toeplitz fixture retained unresolved boundary cells")

/-- Run actual constant, signed monomial, linear, repeated-zero and coupled repeated-root public comparisons. -/
public def run : IO Unit := do
  check "constant" ⟨[⟨⟨1, 1⟩, .nonnegative 0⟩]⟩ 0 0 0 0 0 0 0
  check "z" ⟨[⟨1, .nonnegative 1⟩]⟩ 3 0 1 0 1 0 (-1)
  check "z^-1" ⟨[⟨1, .negative 0⟩]⟩ 0 1 0 0 0 1 1
  check "z^-2" ⟨[⟨1, .negative 1⟩]⟩ 0 2 0 0 0 2 2
  check "z-1/2" ⟨[⟨1, .nonnegative 1⟩, ⟨-(1 / 2), .nonnegative 0⟩]⟩ 5 0 1 0 1 0 (-1)
  check "z-2" ⟨[⟨1, .nonnegative 1⟩, ⟨-2, .nonnegative 0⟩]⟩ 5 0 0 0 0 0 0
  check "z^2" ⟨[⟨1, .nonnegative 2⟩]⟩ 5 0 2 0 2 0 (-2)
  check "coupled" ⟨[⟨1, .nonnegative 2⟩, ⟨-3, .nonnegative 1⟩,
    ⟨9 / 4, .nonnegative 0⟩, ⟨-(1 / 2), .negative 0⟩]⟩ 8 1 2 1 1 0 (-1) true

end TestPurelib.Polynomial.Laurent.Toeplitz
