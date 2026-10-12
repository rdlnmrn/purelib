module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.Fin.Two
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Integral.Transpose
import Purelib.LinearAlgebra.Matrix.Integral.Two
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Topology.Knot.Braid.Artin
public import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Generators
public import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Homology
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Words

public import Purelib.Curves.Legendre.Conventions
import Purelib.Topology.Surface.CellularHomology
public import Purelib.Curves.Legendre.Paths
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Data.Fin.Bijection.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Topology.Surface.CellularHomology.GenusOne.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Paths

open Purelib.LinearAlgebra.Matrix

open Purelib.LinearAlgebra.Matrix.Integral

open Purelib.Topology.Knot

open Purelib.Topology.Knot.Braid.ThreeStrand.Integral

open Purelib.Topology.Surface

public section

/-!
# Certified finite Legendre monodromy

Certified parameter loops are connected to the explicit genus-one homology
action through proof-valued Artin equivalence.  The loops around zero and one
are pure braids (squares of adjacent half-twists).  The infinity loop is the
reverse of their concatenation, so its matrix is derived from the certified
path laws rather than inserted independently.
-/

namespace Purelib.Curves.Legendre.Monodromy

open Purelib.Topology.Knot.Braid
open Purelib.LinearAlgebra

/-- A certified Legendre root chamber at the exact parameter. -/
abbrev Frame (parameter : Paths.Gaussian) :=
  Paths.Frame parameter
/-- A certified parameter path indexed by its original endpoint root frames. -/
abbrev Path {start finish : Paths.Gaussian}
    (left : Frame start) (right : Frame finish) :=
  Paths.Path left right
/-- The integral two-by-two matrix representation of homology transport. -/
abbrev IntegralMatrix := Matrix.Basic.IntegralMatrix

/-- The pure braid consisting of two positive lower adjacent half twists. -/
@[expose] def zeroBraid : Braid.Word 3 :=
  [Conventions.lowerPositive,
    Conventions.lowerPositive]

/-- The pure braid consisting of two positive upper adjacent half twists. -/
@[expose] def oneBraid : Braid.Word 3 :=
  [Conventions.upperPositive,
    Conventions.upperPositive]

/-- The inverse braid of traversal around zero followed by one. -/
@[expose] def infinityBraid : Braid.Word 3 := (zeroBraid ++
  oneBraid).inverse

/-- The standard zero loop fixes every finite branch label. -/
theorem zeroBraid_permutation (label : Fin 3) :
    Curves.Legendre.Monodromy.zeroBraid.permutation.forward label = label := by
  change Conventions.lowerPositive.permutation.forward
      (Conventions.lowerPositive.permutation.forward label) =
    label
  exact Conventions.lowerPositive.permutation_involutive
    label

/-- The standard one loop fixes every finite branch label. -/
theorem oneBraid_permutation (label : Fin 3) :
    Curves.Legendre.Monodromy.oneBraid.permutation.forward label = label := by
  change Conventions.upperPositive.permutation.forward
      (Conventions.upperPositive.permutation.forward label) =
    label
  exact Conventions.upperPositive.permutation_involutive
    label

/-- The explicit integral homology action of the standard zero loop. -/
@[expose] def zeroMatrix : IntegralMatrix := Two.matrix₂ 1 (-2) 0 1
/-- The explicit integral homology action of the standard one loop. -/
@[expose] def oneMatrix : IntegralMatrix := Two.matrix₂ 1 0 2 1
/-- The explicit integral homology action of the inverse combined loop. -/
@[expose] def infinityMatrix : IntegralMatrix := Two.matrix₂ (-3) 2 (-2) 1

/-- Dual matrices acting on columns of periods evaluated on the transported homology basis.

They are transposes of the direct homology actions above. -/
@[expose] def zeroPeriodMatrix : IntegralMatrix := Transpose.transpose zeroMatrix
/-- Transpose the standard one-loop homology matrix to act on period columns. -/
@[expose] def onePeriodMatrix : IntegralMatrix := Transpose.transpose oneMatrix
/-- Transpose the standard infinity-loop homology matrix to act on period columns. -/
@[expose] def infinityPeriodMatrix : IntegralMatrix := Transpose.transpose infinityMatrix

/-- The standard zero-loop dual period action has the displayed integral entries. -/
theorem zeroPeriodMatrix_explicit :
    zeroPeriodMatrix = Two.matrix₂ 1 0 (-2) 1 := by
  unfold zeroPeriodMatrix zeroMatrix
  rw [Transpose.transpose_matrix₂]

/-- The standard one-loop dual period action has the displayed integral entries. -/
theorem onePeriodMatrix_explicit :
    onePeriodMatrix = Two.matrix₂ 1 2 0 1 := by
  unfold onePeriodMatrix oneMatrix
  rw [Transpose.transpose_matrix₂]

/-- The standard infinity-loop dual period action has the displayed integral entries. -/
theorem infinityPeriodMatrix_explicit :
    infinityPeriodMatrix = Two.matrix₂ (-3) (-2) 2 1 := by
  unfold infinityPeriodMatrix infinityMatrix
  rw [Transpose.transpose_matrix₂]

/-- Folding the zero-loop braid gives its explicit homology matrix. -/
theorem zeroBraid_matrix : Words.wordMatrix zeroBraid = zeroMatrix := by
  change Multiplication.mul (Multiplication.mul Multiplication.identity Generators.lowerPositiveMatrix)
    Generators.lowerPositiveMatrix =
    Two.matrix₂ 1 (-2) 0 1
  rw [Multiplication.identity_mul_int]
  unfold Generators.lowerPositiveMatrix
  rw [Two.mul_matrix₂]
  rfl

/-- Folding the one-loop braid gives its explicit homology matrix. -/
theorem oneBraid_matrix : Words.wordMatrix oneBraid = oneMatrix := by
  change Multiplication.mul (Multiplication.mul Multiplication.identity Generators.upperPositiveMatrix)
    Generators.upperPositiveMatrix =
    Two.matrix₂ 1 0 2 1
  rw [Multiplication.identity_mul_int]
  unfold Generators.upperPositiveMatrix
  rw [Two.mul_matrix₂]
  rfl

/-- Folding the inverse combined braid gives the explicit infinity homology matrix. -/
theorem infinityBraid_matrix : Words.wordMatrix infinityBraid = infinityMatrix := by
  change
    Multiplication.mul
      (Multiplication.mul
        (Multiplication.mul
          (Multiplication.mul Multiplication.identity Generators.lowerNegativeMatrix) Generators.lowerNegativeMatrix)
          Generators.upperNegativeMatrix)
        Generators.upperNegativeMatrix = Two.matrix₂ (-3) 2 (-2) 1
  rw [Multiplication.identity_mul_int]
  unfold Generators.lowerNegativeMatrix Generators.upperNegativeMatrix
  rw [Two.mul_matrix₂, Two.mul_matrix₂, Two.mul_matrix₂]
  rfl

/-- The zero-loop braid has the retained dual period matrix. -/
theorem zeroBraid_periodMatrix :
    Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual.periodMatrix zeroBraid =
      zeroPeriodMatrix := by
  unfold Dual.periodMatrix zeroPeriodMatrix
  rw [zeroBraid_matrix]

/-- The one-loop braid has the retained dual period matrix. -/
theorem oneBraid_periodMatrix :
    Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual.periodMatrix oneBraid =
      onePeriodMatrix := by
  unfold Dual.periodMatrix onePeriodMatrix
  rw [oneBraid_matrix]

/-- The infinity-loop braid has the retained dual period matrix. -/
theorem infinityBraid_periodMatrix :
    Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual.periodMatrix infinityBraid =
      infinityPeriodMatrix := by
  unfold Dual.periodMatrix infinityPeriodMatrix
  rw [infinityBraid_matrix]

/-- The infinity homology matrix is a left inverse of the zero-then-one homology action. -/
theorem explicit_loop_product_left :
    Multiplication.mul infinityMatrix (Multiplication.mul
      oneMatrix zeroMatrix) =
      Multiplication.identity := by
  unfold infinityMatrix oneMatrix
    zeroMatrix
  rw [Two.mul_matrix₂, Two.mul_matrix₂]
  apply LinearAlgebra.Matrix.matrix_ext
  intro row column
  rcases Data.Fin.Two.finTwo_cases row with rowZero | rowOne <;>
    rcases Data.Fin.Two.finTwo_cases column with columnZero | columnOne <;>
    subst row <;> subst column <;> rfl

/-- The infinity homology matrix is a right inverse of the zero-then-one homology action. -/
theorem explicit_loop_product_right :
    Multiplication.mul (Multiplication.mul oneMatrix
      zeroMatrix) infinityMatrix =
      Multiplication.identity := by
  unfold infinityMatrix oneMatrix
    zeroMatrix
  rw [Two.mul_matrix₂, Two.mul_matrix₂]
  apply LinearAlgebra.Matrix.matrix_ext
  intro row column
  rcases Data.Fin.Two.finTwo_cases row with rowZero | rowOne <;>
    rcases Data.Fin.Two.finTwo_cases column with columnZero | columnOne <;>
    subst row <;> subst column <;> rfl

/-- In the dual period convention, traversal around zero, then one, then infinity composes as `zeroPeriodMatrix *
onePeriodMatrix * infinityPeriodMatrix`. -/
theorem explicit_period_product_left :
    Multiplication.mul (Multiplication.mul zeroPeriodMatrix
      onePeriodMatrix) infinityPeriodMatrix =
      Multiplication.identity := by
  rw [zeroPeriodMatrix_explicit, onePeriodMatrix_explicit,
    infinityPeriodMatrix_explicit, Two.mul_matrix₂, Two.mul_matrix₂]
  apply LinearAlgebra.Matrix.matrix_ext
  intro row column
  rcases Data.Fin.Two.finTwo_cases row with rowZero | rowOne <;>
    rcases Data.Fin.Two.finTwo_cases column with columnZero | columnOne <;>
    subst row <;> subst column <;> rfl

/-- The infinity dual period matrix is also the left inverse of the combined zero-then-one dual action. -/
theorem explicit_period_product_right :
    Multiplication.mul infinityPeriodMatrix (Multiplication.mul
      zeroPeriodMatrix onePeriodMatrix) =
      Multiplication.identity := by
  rw [zeroPeriodMatrix_explicit, onePeriodMatrix_explicit,
    infinityPeriodMatrix_explicit, Two.mul_matrix₂, Two.mul_matrix₂]
  apply LinearAlgebra.Matrix.matrix_ext
  intro row column
  rcases Data.Fin.Two.finTwo_cases row with rowZero | rowOne <;>
    rcases Data.Fin.Two.finTwo_cases column with columnZero | columnOne <;>
    subst row <;> subst column <;> rfl

set_option genInjectivity false in
/-- Two certified loops based at the same Legendre chamber, together with finite Artin certificates identifying their
extracted words as the standard pure loops around zero and one. -/
structure StandardLoops {parameter : Paths.Gaussian}
    (frame : Frame parameter) where
  /-- The certified zero loop based at the retained original root chamber. -/ zeroPath : Path
    frame frame
  /-- The certified one loop based at the same original root chamber. -/ onePath : Path frame
    frame
  /-- The extracted zero-loop braid is Artin-equivalent to the standard pure zero braid. -/ zeroWord : Artin.Equivalent
    zeroPath.word zeroBraid
  /-- The extracted one-loop braid is Artin-equivalent to the standard pure one braid. -/ oneWord : Artin.Equivalent
    onePath.word oneBraid

constructive_injectivity StandardLoops

namespace StandardLoops

/-- Concatenate the retained zero loop followed by the retained one loop. -/
@[expose] def combinedPath {parameter : Paths.Gaussian}
    {frame : Curves.Legendre.Monodromy.Frame parameter} (loops : Curves.Legendre.Monodromy.StandardLoops frame) :
      Curves.Legendre.Monodromy.Path frame frame :=
  loops.zeroPath.append loops.onePath

/-- The infinity loop is not extra remembered data: it is path reversal of the zero-then-one product under the locked
concatenation convention. -/
@[expose] def infinityPath {parameter : Paths.Gaussian}
    {frame : Curves.Legendre.Monodromy.Frame parameter} (loops : Curves.Legendre.Monodromy.StandardLoops frame) :
      Curves.Legendre.Monodromy.Path frame frame :=
  loops.combinedPath.reverse

/-- Concatenate the combined zero-then-one path with its reversed infinity path. -/
@[expose] def productPath {parameter : Paths.Gaussian}
    {frame : Curves.Legendre.Monodromy.Frame parameter} (loops : Curves.Legendre.Monodromy.StandardLoops frame) :
      Curves.Legendre.Monodromy.Path frame frame :=
  loops.combinedPath.append loops.infinityPath

/-- The retained certified zero path has the standard homology action. -/
theorem zeroPath_matrix {parameter : Paths.Gaussian}
    {frame : Curves.Legendre.Monodromy.Frame parameter} (loops : Curves.Legendre.Monodromy.StandardLoops frame) :
    Words.wordMatrix loops.zeroPath.word = zeroMatrix :=
  (Words.equivalent_matrix_eq loops.zeroWord).trans Curves.Legendre.Monodromy.zeroBraid_matrix

/-- The retained certified one path has the standard homology action. -/
theorem onePath_matrix {parameter : Paths.Gaussian}
    {frame : Curves.Legendre.Monodromy.Frame parameter} (loops : Curves.Legendre.Monodromy.StandardLoops frame) :
    Words.wordMatrix loops.onePath.word = oneMatrix :=
  (Words.equivalent_matrix_eq loops.oneWord).trans Curves.Legendre.Monodromy.oneBraid_matrix

/-- The retained certified zero path has the standard dual period action. -/
theorem zeroPath_periodMatrix
    {parameter : Paths.Gaussian}
    {frame : Curves.Legendre.Monodromy.Frame parameter} (loops : Curves.Legendre.Monodromy.StandardLoops frame) :
    Dual.periodMatrix loops.zeroPath.word = zeroPeriodMatrix :=
  (Dual.equivalent_periodMatrix_eq loops.zeroWord).trans Curves.Legendre.Monodromy.zeroBraid_periodMatrix

/-- The retained certified one path has the standard dual period action. -/
theorem onePath_periodMatrix
    {parameter : Paths.Gaussian}
    {frame : Curves.Legendre.Monodromy.Frame parameter} (loops : Curves.Legendre.Monodromy.StandardLoops frame) :
    Dual.periodMatrix loops.onePath.word = onePeriodMatrix :=
  (Dual.equivalent_periodMatrix_eq loops.oneWord).trans Curves.Legendre.Monodromy.oneBraid_periodMatrix

/-- The combined retained path acts by the ordered product of the one and zero homology matrices. -/
theorem combinedPath_matrix {parameter : Paths.Gaussian}
    {frame : Curves.Legendre.Monodromy.Frame parameter} (loops : Curves.Legendre.Monodromy.StandardLoops frame) :
    Words.wordMatrix loops.combinedPath.word = Multiplication.mul Curves.Legendre.Monodromy.oneMatrix zeroMatrix := by
  rw [combinedPath, Path.word_append,
    Words.wordMatrix_append, loops.zeroPath_matrix, loops.onePath_matrix]

/-- Reversing a certified path gives a two-sided inverse homology matrix. -/
theorem reversePath_matrix_identities
    {start finish : Paths.Gaussian}
    {left : Curves.Legendre.Monodromy.Frame start} {right : Curves.Legendre.Monodromy.Frame finish} (path :
      Curves.Legendre.Monodromy.Path left right) :
    Multiplication.mul (Words.wordMatrix path.reverse.word) (Words.wordMatrix path.word) = Multiplication.identity ∧
      Multiplication.mul (Words.wordMatrix path.word) (Words.wordMatrix path.reverse.word) = Multiplication.identity :=
        by
  rw [Path.word_reverse]
  exact Words.wordMatrix_inverse_identities path.word

/-- The infinity matrix follows from reversal and the already certified zero and one matrices. -/
theorem infinityPath_matrix
    {parameter : Paths.Gaussian}
    {frame : Curves.Legendre.Monodromy.Frame parameter} (loops : Curves.Legendre.Monodromy.StandardLoops frame) :
    Words.wordMatrix loops.infinityPath.word = infinityMatrix := by
  have reverseLeft := (reversePath_matrix_identities loops.combinedPath).1
  change Multiplication.mul (Words.wordMatrix loops.infinityPath.word)
      (Words.wordMatrix loops.combinedPath.word) = Multiplication.identity at reverseLeft
  have combined := loops.combinedPath_matrix
  calc
    Words.wordMatrix loops.infinityPath.word =
        Multiplication.mul (Words.wordMatrix loops.infinityPath.word) Multiplication.identity :=
      (Multiplication.mul_identity_int _).symm
    _ = Multiplication.mul (Words.wordMatrix loops.infinityPath.word)
          (Multiplication.mul (Words.wordMatrix loops.combinedPath.word) Curves.Legendre.Monodromy.infinityMatrix) := by
      rw [combined, Curves.Legendre.Monodromy.explicit_loop_product_right]
    _ = Multiplication.mul
          (Multiplication.mul (Words.wordMatrix loops.infinityPath.word)
            (Words.wordMatrix loops.combinedPath.word)) infinityMatrix :=
      (Multiplication.mul_assoc _ _ _).symm
    _ = Multiplication.mul Multiplication.identity infinityMatrix := by rw [reverseLeft]
    _ = infinityMatrix := Multiplication.identity_mul_int _

/-- The derived reversed infinity path has the standard dual period action. -/
theorem infinityPath_periodMatrix
    {parameter : Paths.Gaussian}
    {frame : Curves.Legendre.Monodromy.Frame parameter} (loops : Curves.Legendre.Monodromy.StandardLoops frame) :
    Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual.periodMatrix loops.infinityPath.word = infinityPeriodMatrix :=
      by
  unfold Dual.periodMatrix Curves.Legendre.Monodromy.infinityPeriodMatrix
  rw [loops.infinityPath_matrix]

/-- The retained combined path followed by its reverse has identity homology action. -/
theorem productPath_matrix
    {parameter : Paths.Gaussian}
    {frame : Curves.Legendre.Monodromy.Frame parameter} (loops : Curves.Legendre.Monodromy.StandardLoops frame) :
    Words.wordMatrix loops.productPath.word = Multiplication.identity := by
  rw [productPath, Path.word_append,
    Words.wordMatrix_append, loops.infinityPath_matrix,
    loops.combinedPath_matrix, Curves.Legendre.Monodromy.explicit_loop_product_left]

/-- The retained combined path followed by its reverse has identity dual period action. -/
theorem productPath_periodMatrix
    {parameter : Paths.Gaussian}
    {frame : Curves.Legendre.Monodromy.Frame parameter} (loops : Curves.Legendre.Monodromy.StandardLoops frame) :
    Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual.periodMatrix loops.productPath.word = Multiplication.identity
      := by
  unfold Dual.periodMatrix
  rw [loops.productPath_matrix, Transpose.transpose_identity]

/-- The certified zero loop returns every original root owner to itself. -/
theorem zero_root_transport
    {parameter : Paths.Gaussian}
    {frame : Curves.Legendre.Monodromy.Frame parameter} (loops : Curves.Legendre.Monodromy.StandardLoops frame) (label :
      Fin 3) :
    loops.zeroPath.ownerTransport.forward (frame.labels.forward label) =
      frame.labels.forward label := by
  let position := frame.projected.orderToOwner.backward
    (frame.labels.forward label)
  have ownerEq : frame.projected.ownerIndex position =
      frame.labels.forward label :=
    frame.projected.orderToOwner.forward_backward (frame.labels.forward label)
  have wordFixed : loops.zeroPath.word.permutation.forward position =
      position :=
    (loops.zeroWord.permutationSame position).trans
      (Curves.Legendre.Monodromy.zeroBraid_permutation position)
  rw [← ownerEq]
  exact (loops.zeroPath.ownerTransport_agrees position).trans
    (congrArg frame.projected.ownerIndex wordFixed)

/-- The certified one loop returns every original root owner to itself. -/
theorem one_root_transport
    {parameter : Paths.Gaussian}
    {frame : Curves.Legendre.Monodromy.Frame parameter} (loops : Curves.Legendre.Monodromy.StandardLoops frame) (label :
      Fin 3) :
    loops.onePath.ownerTransport.forward (frame.labels.forward label) =
      frame.labels.forward label := by
  let position := frame.projected.orderToOwner.backward
    (frame.labels.forward label)
  have ownerEq : frame.projected.ownerIndex position =
      frame.labels.forward label :=
    frame.projected.orderToOwner.forward_backward (frame.labels.forward label)
  have wordFixed : loops.onePath.word.permutation.forward position =
      position :=
    (loops.oneWord.permutationSame position).trans
      (Curves.Legendre.Monodromy.oneBraid_permutation position)
  rw [← ownerEq]
  exact (loops.onePath.ownerTransport_agrees position).trans
    (congrArg frame.projected.ownerIndex wordFixed)

/-- The first finite headline package: root transport, integral symplectic Picard--Lefschetz matrices, reversal, and the
loop-product relation all come from the same certified paths. -/
structure Certificate {parameter : Paths.Gaussian}
    {frame : Curves.Legendre.Monodromy.Frame parameter} (loops : Curves.Legendre.Monodromy.StandardLoops frame) : Prop
      where
  /-- The retained zero loop fixes each original labelled root owner. -/ zeroRoots : forall label,
    loops.zeroPath.ownerTransport.forward
    (frame.labels.forward label) = frame.labels.forward label
  /-- The retained one loop fixes each original labelled root owner. -/ oneRoots : forall label,
    loops.onePath.ownerTransport.forward
    (frame.labels.forward label) = frame.labels.forward label
  /-- The zero path realizes the displayed zero homology matrix. -/ zeroAction : Words.wordMatrix loops.zeroPath.word =
    Curves.Legendre.Monodromy.zeroMatrix
  /-- The one path realizes the displayed one homology matrix. -/ oneAction : Words.wordMatrix loops.onePath.word =
    Curves.Legendre.Monodromy.oneMatrix
  /-- The derived infinity path realizes the displayed infinity homology matrix. -/ infinityAction : Words.wordMatrix
    loops.infinityPath.word = Curves.Legendre.Monodromy.infinityMatrix
  /-- The concatenated loop product realizes the identity homology matrix. -/ productAction : Words.wordMatrix
    loops.productPath.word = Multiplication.identity
  /-- The zero path realizes the displayed zero dual period matrix. -/ zeroPeriodAction : Dual.periodMatrix
    loops.zeroPath.word = Curves.Legendre.Monodromy.zeroPeriodMatrix
  /-- The one path realizes the displayed one dual period matrix. -/ onePeriodAction : Dual.periodMatrix
    loops.onePath.word = Curves.Legendre.Monodromy.onePeriodMatrix
  /-- The derived infinity path realizes the displayed infinity dual period matrix. -/ infinityPeriodAction :
    Dual.periodMatrix loops.infinityPath.word = Curves.Legendre.Monodromy.infinityPeriodMatrix
  /-- The concatenated loop product realizes the identity dual period matrix. -/ productPeriodAction : Dual.periodMatrix
    loops.productPath.word = Multiplication.identity
  /-- Transport around zero preserves the integral homology intersection pairing. -/ zeroSymplectic : forall left right,
    CellularHomology.intersection
        (Homology.actWord loops.zeroPath.word left) (Homology.actWord loops.zeroPath.word right) =
      CellularHomology.intersection left right
  /-- Transport around one preserves the integral homology intersection pairing. -/ oneSymplectic : forall left right,
    CellularHomology.intersection
        (Homology.actWord loops.onePath.word left) (Homology.actWord loops.onePath.word right) =
      CellularHomology.intersection left right
  /-- Transport around infinity preserves the integral homology intersection pairing. -/ infinitySymplectic : forall
    left right,
    CellularHomology.intersection
        (Homology.actWord loops.infinityPath.word left)
        (Homology.actWord loops.infinityPath.word right) =
      CellularHomology.intersection left right

/-- Assemble the root, homology, period and intersection guarantees of the same retained standard paths.

The infinity and product guarantees are derived from path reversal and concatenation, while the Artin witnesses identify
the zero and one actions. -/
theorem certificate {parameter : Paths.Gaussian}
    {frame : Curves.Legendre.Monodromy.Frame parameter} (loops : Curves.Legendre.Monodromy.StandardLoops frame) :
    Certificate loops where
  zeroRoots := loops.zero_root_transport
  oneRoots := loops.one_root_transport
  zeroAction := loops.zeroPath_matrix
  oneAction := loops.onePath_matrix
  infinityAction := loops.infinityPath_matrix
  productAction := loops.productPath_matrix
  zeroPeriodAction := loops.zeroPath_periodMatrix
  onePeriodAction := loops.onePath_periodMatrix
  infinityPeriodAction := loops.infinityPath_periodMatrix
  productPeriodAction := loops.productPath_periodMatrix
  zeroSymplectic := Homology.word_preserves_intersection loops.zeroPath.word
  oneSymplectic := Homology.word_preserves_intersection loops.onePath.word
  infinitySymplectic := Homology.word_preserves_intersection loops.infinityPath.word

end StandardLoops

end Purelib.Curves.Legendre.Monodromy
