import CCL.Riemann.LegendrePaths
import CCL.Riemann.LegendrePicardLefschetz

/-!
# Certified finite Legendre monodromy

Certified parameter loops are connected to the explicit genus-one homology
action through proof-valued Artin equivalence.  The loops around zero and one
are pure braids (squares of adjacent half-twists).  The infinity loop is the
reverse of their concatenation, so its matrix is derived from the certified
path laws rather than inserted independently.
-/

namespace CCL.Riemann.LegendreMonodromy

open CCL.Knot.FiniteBraid
open RFAP.ConstructiveFiniteMatrix
open CCL.Riemann.LegendrePicardLefschetz

abbrev Frame (parameter : CCL.Riemann.LegendrePaths.Gaussian) :=
  CCL.Riemann.LegendrePaths.Frame parameter
abbrev Path {start finish : CCL.Riemann.LegendrePaths.Gaussian}
    (left : Frame start) (right : Frame finish) :=
  CCL.Riemann.LegendrePaths.Path left right
abbrev IntegralMatrix := CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix

def zeroBraid : Word 3 :=
  [CCL.Riemann.LegendreConventions.lowerPositive,
    CCL.Riemann.LegendreConventions.lowerPositive]

def oneBraid : Word 3 :=
  [CCL.Riemann.LegendreConventions.upperPositive,
    CCL.Riemann.LegendreConventions.upperPositive]

def infinityBraid : Word 3 := (zeroBraid ++ oneBraid).inverse

theorem zeroBraid_permutation (label : Fin 3) :
    zeroBraid.permutation.forward label = label := by
  change CCL.Riemann.LegendreConventions.lowerPositive.permutation.forward
      (CCL.Riemann.LegendreConventions.lowerPositive.permutation.forward label) =
    label
  exact CCL.Riemann.LegendreConventions.lowerPositive.permutation_involutive
    label

theorem oneBraid_permutation (label : Fin 3) :
    oneBraid.permutation.forward label = label := by
  change CCL.Riemann.LegendreConventions.upperPositive.permutation.forward
      (CCL.Riemann.LegendreConventions.upperPositive.permutation.forward label) =
    label
  exact CCL.Riemann.LegendreConventions.upperPositive.permutation_involutive
    label

def zeroMatrix : IntegralMatrix := matrix₂ 1 (-2) 0 1
def oneMatrix : IntegralMatrix := matrix₂ 1 0 2 1
def infinityMatrix : IntegralMatrix := matrix₂ (-3) 2 (-2) 1

/-- Dual matrices acting on columns of periods evaluated on the transported
homology basis.  They are transposes of the direct homology actions above. -/
def zeroPeriodMatrix : IntegralMatrix := transpose zeroMatrix
def onePeriodMatrix : IntegralMatrix := transpose oneMatrix
def infinityPeriodMatrix : IntegralMatrix := transpose infinityMatrix

theorem zeroPeriodMatrix_explicit :
    zeroPeriodMatrix = matrix₂ 1 0 (-2) 1 := by
  unfold zeroPeriodMatrix zeroMatrix
  rw [transpose_matrix₂]

theorem onePeriodMatrix_explicit :
    onePeriodMatrix = matrix₂ 1 2 0 1 := by
  unfold onePeriodMatrix oneMatrix
  rw [transpose_matrix₂]

theorem infinityPeriodMatrix_explicit :
    infinityPeriodMatrix = matrix₂ (-3) (-2) 2 1 := by
  unfold infinityPeriodMatrix infinityMatrix
  rw [transpose_matrix₂]

theorem zeroBraid_matrix : wordMatrix zeroBraid = zeroMatrix := by
  change mul (mul identity lowerPositiveMatrix) lowerPositiveMatrix =
    matrix₂ 1 (-2) 0 1
  rw [identity_mul_int]
  unfold lowerPositiveMatrix
  rw [mul_matrix₂]
  rfl

theorem oneBraid_matrix : wordMatrix oneBraid = oneMatrix := by
  change mul (mul identity upperPositiveMatrix) upperPositiveMatrix =
    matrix₂ 1 0 2 1
  rw [identity_mul_int]
  unfold upperPositiveMatrix
  rw [mul_matrix₂]
  rfl

theorem infinityBraid_matrix : wordMatrix infinityBraid = infinityMatrix := by
  change
    mul
      (mul
        (mul
          (mul identity lowerNegativeMatrix) lowerNegativeMatrix)
          upperNegativeMatrix)
        upperNegativeMatrix = matrix₂ (-3) 2 (-2) 1
  rw [identity_mul_int]
  unfold lowerNegativeMatrix upperNegativeMatrix
  rw [mul_matrix₂, mul_matrix₂, mul_matrix₂]
  rfl

theorem zeroBraid_periodMatrix :
    periodMatrix zeroBraid = zeroPeriodMatrix := by
  unfold periodMatrix zeroPeriodMatrix
  rw [zeroBraid_matrix]

theorem oneBraid_periodMatrix :
    periodMatrix oneBraid = onePeriodMatrix := by
  unfold periodMatrix onePeriodMatrix
  rw [oneBraid_matrix]

theorem infinityBraid_periodMatrix :
    periodMatrix infinityBraid = infinityPeriodMatrix := by
  unfold periodMatrix infinityPeriodMatrix
  rw [infinityBraid_matrix]

theorem explicit_loop_product_left :
    mul infinityMatrix (mul oneMatrix zeroMatrix) = identity := by
  unfold infinityMatrix oneMatrix zeroMatrix
  rw [mul_matrix₂, mul_matrix₂]
  apply matrix_ext
  intro row column
  have rowCases : row = 0 ∨ row = 1 := by
    rcases row with ⟨value, bound⟩
    omega0
  have columnCases : column = 0 ∨ column = 1 := by
    rcases column with ⟨value, bound⟩
    omega0
  rcases rowCases with rowZero | rowOne <;>
    rcases columnCases with columnZero | columnOne <;>
    subst row <;> subst column <;> rfl

theorem explicit_loop_product_right :
    mul (mul oneMatrix zeroMatrix) infinityMatrix = identity := by
  unfold infinityMatrix oneMatrix zeroMatrix
  rw [mul_matrix₂, mul_matrix₂]
  apply matrix_ext
  intro row column
  have rowCases : row = 0 ∨ row = 1 := by
    rcases row with ⟨value, bound⟩
    omega0
  have columnCases : column = 0 ∨ column = 1 := by
    rcases column with ⟨value, bound⟩
    omega0
  rcases rowCases with rowZero | rowOne <;>
    rcases columnCases with columnZero | columnOne <;>
    subst row <;> subst column <;> rfl

/-- In the dual period convention, traversal around zero, then one, then
infinity composes as `zeroPeriodMatrix * onePeriodMatrix *
infinityPeriodMatrix`. -/
theorem explicit_period_product_left :
    mul (mul zeroPeriodMatrix onePeriodMatrix) infinityPeriodMatrix =
      identity := by
  rw [zeroPeriodMatrix_explicit, onePeriodMatrix_explicit,
    infinityPeriodMatrix_explicit, mul_matrix₂, mul_matrix₂]
  apply matrix_ext
  intro row column
  have rowCases : row = 0 ∨ row = 1 := by
    rcases row with ⟨value, bound⟩
    omega0
  have columnCases : column = 0 ∨ column = 1 := by
    rcases column with ⟨value, bound⟩
    omega0
  rcases rowCases with rowZero | rowOne <;>
    rcases columnCases with columnZero | columnOne <;>
    subst row <;> subst column <;> rfl

/-- The infinity dual period matrix is also the left inverse of the combined
zero-then-one dual action. -/
theorem explicit_period_product_right :
    mul infinityPeriodMatrix (mul zeroPeriodMatrix onePeriodMatrix) =
      identity := by
  rw [zeroPeriodMatrix_explicit, onePeriodMatrix_explicit,
    infinityPeriodMatrix_explicit, mul_matrix₂, mul_matrix₂]
  apply matrix_ext
  intro row column
  have rowCases : row = 0 ∨ row = 1 := by
    rcases row with ⟨value, bound⟩
    omega0
  have columnCases : column = 0 ∨ column = 1 := by
    rcases column with ⟨value, bound⟩
    omega0
  rcases rowCases with rowZero | rowOne <;>
    rcases columnCases with columnZero | columnOne <;>
    subst row <;> subst column <;> rfl

/-- Two certified loops based at the same Legendre chamber, together with
finite Artin certificates identifying their extracted words as the standard
pure loops around zero and one. -/
structure StandardLoops {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    (frame : Frame parameter) where
  zeroPath : Path frame frame
  onePath : Path frame frame
  zeroWord : CCL.Knot.ArtinRelations.Equivalent zeroPath.word zeroBraid
  oneWord : CCL.Knot.ArtinRelations.Equivalent onePath.word oneBraid

namespace StandardLoops

def combinedPath {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    {frame : Frame parameter} (loops : StandardLoops frame) : Path frame frame :=
  loops.zeroPath.append loops.onePath

/-- The infinity loop is not extra remembered data: it is path reversal of
the zero-then-one product under the locked concatenation convention. -/
def infinityPath {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    {frame : Frame parameter} (loops : StandardLoops frame) : Path frame frame :=
  loops.combinedPath.reverse

def productPath {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    {frame : Frame parameter} (loops : StandardLoops frame) : Path frame frame :=
  loops.combinedPath.append loops.infinityPath

theorem zeroPath_matrix {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    {frame : Frame parameter} (loops : StandardLoops frame) :
    wordMatrix loops.zeroPath.word = zeroMatrix :=
  (equivalent_matrix_eq loops.zeroWord).trans zeroBraid_matrix

theorem onePath_matrix {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    {frame : Frame parameter} (loops : StandardLoops frame) :
    wordMatrix loops.onePath.word = oneMatrix :=
  (equivalent_matrix_eq loops.oneWord).trans oneBraid_matrix

theorem zeroPath_periodMatrix
    {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    {frame : Frame parameter} (loops : StandardLoops frame) :
    periodMatrix loops.zeroPath.word = zeroPeriodMatrix :=
  (equivalent_periodMatrix_eq loops.zeroWord).trans zeroBraid_periodMatrix

theorem onePath_periodMatrix
    {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    {frame : Frame parameter} (loops : StandardLoops frame) :
    periodMatrix loops.onePath.word = onePeriodMatrix :=
  (equivalent_periodMatrix_eq loops.oneWord).trans oneBraid_periodMatrix

theorem combinedPath_matrix {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    {frame : Frame parameter} (loops : StandardLoops frame) :
    wordMatrix loops.combinedPath.word = mul oneMatrix zeroMatrix := by
  rw [combinedPath, CCL.Riemann.LegendrePaths.Path.word_append,
    wordMatrix_append, loops.zeroPath_matrix, loops.onePath_matrix]

theorem reversePath_matrix_identities
    {start finish : CCL.Riemann.LegendrePaths.Gaussian}
    {left : Frame start} {right : Frame finish} (path : Path left right) :
    mul (wordMatrix path.reverse.word) (wordMatrix path.word) = identity ∧
      mul (wordMatrix path.word) (wordMatrix path.reverse.word) = identity := by
  rw [CCL.Riemann.LegendrePaths.Path.word_reverse]
  exact wordMatrix_inverse_identities path.word

/-- The infinity matrix follows from reversal and the already certified zero
and one matrices. -/
theorem infinityPath_matrix
    {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    {frame : Frame parameter} (loops : StandardLoops frame) :
    wordMatrix loops.infinityPath.word = infinityMatrix := by
  have reverseLeft := (reversePath_matrix_identities loops.combinedPath).1
  change mul (wordMatrix loops.infinityPath.word)
      (wordMatrix loops.combinedPath.word) = identity at reverseLeft
  have combined := loops.combinedPath_matrix
  calc
    wordMatrix loops.infinityPath.word =
        mul (wordMatrix loops.infinityPath.word) identity :=
      (mul_identity_int _).symm
    _ = mul (wordMatrix loops.infinityPath.word)
          (mul (wordMatrix loops.combinedPath.word) infinityMatrix) := by
      rw [combined, explicit_loop_product_right]
    _ = mul
          (mul (wordMatrix loops.infinityPath.word)
            (wordMatrix loops.combinedPath.word)) infinityMatrix :=
      (RFAP.ConstructiveFiniteMatrix.mul_assoc _ _ _).symm
    _ = mul identity infinityMatrix := by rw [reverseLeft]
    _ = infinityMatrix := identity_mul_int _

theorem infinityPath_periodMatrix
    {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    {frame : Frame parameter} (loops : StandardLoops frame) :
    periodMatrix loops.infinityPath.word = infinityPeriodMatrix := by
  unfold periodMatrix infinityPeriodMatrix
  rw [loops.infinityPath_matrix]

theorem productPath_matrix
    {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    {frame : Frame parameter} (loops : StandardLoops frame) :
    wordMatrix loops.productPath.word = identity := by
  rw [productPath, CCL.Riemann.LegendrePaths.Path.word_append,
    wordMatrix_append, loops.infinityPath_matrix,
    loops.combinedPath_matrix, explicit_loop_product_left]

theorem productPath_periodMatrix
    {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    {frame : Frame parameter} (loops : StandardLoops frame) :
    periodMatrix loops.productPath.word = identity := by
  unfold periodMatrix
  rw [loops.productPath_matrix, transpose_identity]

theorem zero_root_transport
    {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    {frame : Frame parameter} (loops : StandardLoops frame) (label : Fin 3) :
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
      (zeroBraid_permutation position)
  rw [← ownerEq]
  exact (loops.zeroPath.ownerTransport_agrees position).trans
    (congrArg frame.projected.ownerIndex wordFixed)

theorem one_root_transport
    {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    {frame : Frame parameter} (loops : StandardLoops frame) (label : Fin 3) :
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
      (oneBraid_permutation position)
  rw [← ownerEq]
  exact (loops.onePath.ownerTransport_agrees position).trans
    (congrArg frame.projected.ownerIndex wordFixed)

/-- The first finite headline package: root transport, integral symplectic
Picard--Lefschetz matrices, reversal, and the loop-product relation all come
from the same certified paths. -/
structure Certificate {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    {frame : Frame parameter} (loops : StandardLoops frame) : Prop where
  zeroRoots : forall label, loops.zeroPath.ownerTransport.forward
    (frame.labels.forward label) = frame.labels.forward label
  oneRoots : forall label, loops.onePath.ownerTransport.forward
    (frame.labels.forward label) = frame.labels.forward label
  zeroAction : wordMatrix loops.zeroPath.word = zeroMatrix
  oneAction : wordMatrix loops.onePath.word = oneMatrix
  infinityAction : wordMatrix loops.infinityPath.word = infinityMatrix
  productAction : wordMatrix loops.productPath.word = identity
  zeroPeriodAction : periodMatrix loops.zeroPath.word = zeroPeriodMatrix
  onePeriodAction : periodMatrix loops.onePath.word = onePeriodMatrix
  infinityPeriodAction :
    periodMatrix loops.infinityPath.word = infinityPeriodMatrix
  productPeriodAction : periodMatrix loops.productPath.word = identity
  zeroSymplectic : forall left right,
    CCL.Riemann.CellularHomology.intersection
        (actWord loops.zeroPath.word left) (actWord loops.zeroPath.word right) =
      CCL.Riemann.CellularHomology.intersection left right
  oneSymplectic : forall left right,
    CCL.Riemann.CellularHomology.intersection
        (actWord loops.onePath.word left) (actWord loops.onePath.word right) =
      CCL.Riemann.CellularHomology.intersection left right
  infinitySymplectic : forall left right,
    CCL.Riemann.CellularHomology.intersection
        (actWord loops.infinityPath.word left)
        (actWord loops.infinityPath.word right) =
      CCL.Riemann.CellularHomology.intersection left right

theorem certificate {parameter : CCL.Riemann.LegendrePaths.Gaussian}
    {frame : Frame parameter} (loops : StandardLoops frame) :
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
  zeroSymplectic := word_preserves_intersection loops.zeroPath.word
  oneSymplectic := word_preserves_intersection loops.onePath.word
  infinitySymplectic := word_preserves_intersection loops.infinityPath.word

end StandardLoops

end CCL.Riemann.LegendreMonodromy
