import CCL.Progressive.FiniteMonodromy
import CCL.Progressive.GaussianIntegration
import CCL.Riemann.CellularHomology

/-!
# Finite sheet-aware paths for period integration

A lifted path below is an inductive finite chain.  Every geometric edge
carries an explicit permutation of the labelled sheets and a proof that the
chosen endpoint sheet is the transported start sheet.  A separate inductive
relation verifies that a progressive integration model follows exactly the
same displayed geometric edges.  This separation lets several algebraic
differentials share one persistent lifted cycle while retaining their own
local polynomial integrand models.
-/

namespace CCL.Riemann.LiftedPaths

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev FiniteBijection := CCL.FiniteMonodromy.FiniteBijection
abbrev CellModel := CCL.ProgressiveGaussianIntegration.CellModel
abbrev PathModel := CCL.ProgressiveGaussianIntegration.PathModel
abbrev RefinementProgram :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed

/-- One displayed point of the base path together with its labelled sheet. -/
structure LiftedPoint (sheets : Nat) where
  coordinate : Gaussian
  sheet : Fin sheets

/-- One finite geometric edge and its certified sheet transport. -/
structure LiftedCell {sheets : Nat}
    (start finish : LiftedPoint sheets) where
  sheetTransport : FiniteBijection sheets sheets
  finishSheet_eq : sheetTransport.forward start.sheet = finish.sheet

namespace LiftedCell

/-- Reverse one displayed lifted edge, including its finite sheet
permutation.  The endpoint sheet equation follows by applying the stored
backward map to the original forward equation. -/
def reverse {sheets : Nat} {start finish : LiftedPoint sheets}
    (cell : LiftedCell start finish) : LiftedCell finish start where
  sheetTransport := cell.sheetTransport.reverse
  finishSheet_eq := by
    change cell.sheetTransport.backward finish.sheet = start.sheet
    rw [← cell.finishSheet_eq]
    exact cell.sheetTransport.backward_forward start.sheet

end LiftedCell

/-- A finite path whose dependent endpoints enforce geometric and sheet
continuity between consecutive cells. -/
inductive LiftedPath (sheets : Nat) :
    LiftedPoint sheets -> LiftedPoint sheets -> Type
  | nil (point : LiftedPoint sheets) : LiftedPath sheets point point
  | cons {start middle finish : LiftedPoint sheets}
      (cell : LiftedCell start middle)
      (remaining : LiftedPath sheets middle finish) :
      LiftedPath sheets start finish

namespace LiftedPath

def cellCount {sheets : Nat} : {start finish : LiftedPoint sheets} ->
    LiftedPath sheets start finish -> Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ remaining => remaining.cellCount + 1

/-- Append two finite lifted paths with the same displayed middle point. -/
def append {sheets : Nat}
    {start middle finish : LiftedPoint sheets}
    (first : LiftedPath sheets start middle)
    (second : LiftedPath sheets middle finish) :
    LiftedPath sheets start finish :=
  match first with
  | .nil _ => second
  | .cons cell remaining => .cons cell (remaining.append second)

/-- Reverse a finite lifted path in the literal cell order.  No completed
path or quotient on paths is used: the recursion materializes the reversed
finite chain and reverses each displayed sheet permutation. -/
def reverse {sheets : Nat} : {start finish : LiftedPoint sheets} ->
    LiftedPath sheets start finish -> LiftedPath sheets finish start
  | _, _, .nil point => .nil point
  | _, _, .cons cell remaining =>
      remaining.reverse.append (.cons cell.reverse (.nil _))

/-- Change only the propositionally equal starting lifted-point index. -/
def castStart {sheets : Nat}
    {left right finish : LiftedPoint sheets} (equal : left = right)
    (path : LiftedPath sheets left finish) :
    LiftedPath sheets right finish := by
  subst right
  exact path

/-- Change only the propositionally equal finishing lifted-point index. -/
def castFinish {sheets : Nat}
    {start left right : LiftedPoint sheets} (equal : left = right)
    (path : LiftedPath sheets start left) :
    LiftedPath sheets start right := by
  subst right
  exact path

@[simp] theorem cellCount_append {sheets : Nat}
    {start middle finish : LiftedPoint sheets}
    (first : LiftedPath sheets start middle)
    (second : LiftedPath sheets middle finish) :
    (first.append second).cellCount = first.cellCount + second.cellCount := by
  induction first with
  | nil => simp only [append, cellCount, Nat.zero_add]
  | cons cell remaining inductionHypothesis =>
      simp only [append, cellCount, inductionHypothesis]
      omega0

/-- Compose every displayed local sheet permutation in path order. -/
def sheetTransport {sheets : Nat} :
    {start finish : LiftedPoint sheets} ->
      LiftedPath sheets start finish -> FiniteBijection sheets sheets
  | _, _, .nil _ => CCL.FiniteMonodromy.FiniteBijection.identity sheets
  | _, _, .cons cell remaining =>
      CCL.FiniteMonodromy.FiniteBijection.comp
        remaining.sheetTransport cell.sheetTransport

/-- The composed permutation carries the initial sheet to the final sheet. -/
theorem sheetTransport_start {sheets : Nat}
    {start finish : LiftedPoint sheets}
    (path : LiftedPath sheets start finish) :
    path.sheetTransport.forward start.sheet = finish.sheet := by
  induction path with
  | nil point => rfl
  | cons cell remaining inductionHypothesis =>
      change remaining.sheetTransport.forward
        (cell.sheetTransport.forward _) = _
      rw [cell.finishSheet_eq, inductionHypothesis]

/-- Cell-by-cell evidence that a list of integration cells follows a lifted
geometric path. -/
inductive FollowedBy {sheets : Nat} :
    List CellModel -> {start finish : LiftedPoint sheets} ->
      LiftedPath sheets start finish -> Prop
  | nil (point : LiftedPoint sheets) : FollowedBy [] (.nil point)
  | cons {start middle finish : LiftedPoint sheets}
      {model : CellModel} {models : List CellModel}
      {cell : LiftedCell start middle}
      {remaining : LiftedPath sheets middle finish}
      (start_eq : model.start = start.coordinate)
      (finish_eq : model.finish = middle.coordinate)
      (tail : FollowedBy models remaining) :
      FollowedBy (model :: models) (.cons cell remaining)

theorem followedBy_length {sheets : Nat} {models : List CellModel}
    {start finish : LiftedPoint sheets} {path : LiftedPath sheets start finish}
    (follows : FollowedBy models path) :
    models.length = path.cellCount := by
  induction follows with
  | nil => rfl
  | cons start_eq finish_eq tail inductionHypothesis =>
      simp only [List.length_cons, cellCount, inductionHypothesis]

/-- Exact finite telescoping of the affine displacements in any model that
follows a lifted path.  This is the geometric identity used when a block of
fine prepared cells is certified as a partition of one coarser cell. -/
theorem followedBy_displacementSum {sheets : Nat}
    {models : List CellModel}
    {start finish : LiftedPoint sheets}
    {path : LiftedPath sheets start finish}
    (follows : FollowedBy models path) :
    CCL.ProgressiveGaussianIntegration.PathModel.displacementSum models =
      finish.coordinate - start.coordinate := by
  induction follows with
  | nil point =>
      simp only [CCL.ProgressiveGaussianIntegration.PathModel.displacementSum,
        List.foldr_nil, RFAP.ConstructiveGaussian.Gaussian.sub_self]
  | @cons start middle finish model models cell remaining start_eq finish_eq
      tail inductionHypothesis =>
      simp only [CCL.ProgressiveGaussianIntegration.PathModel.displacementSum_cons]
      unfold CCL.ProgressiveGaussianIntegration.CellModel.displacement
      rw [start_eq, finish_eq, inductionHypothesis]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1

theorem followedBy_append {sheets : Nat}
    {firstModels secondModels : List CellModel}
    {start middle finish : LiftedPoint sheets}
    {first : LiftedPath sheets start middle}
    {second : LiftedPath sheets middle finish}
    (firstFollows : FollowedBy firstModels first)
    (secondFollows : FollowedBy secondModels second) :
    FollowedBy (firstModels ++ secondModels) (first.append second) := by
  induction firstFollows with
  | nil => exact secondFollows
  | cons start_eq finish_eq tail inductionHypothesis =>
      exact .cons start_eq finish_eq (inductionHypothesis secondFollows)

/-- Cellwise reversal evidence follows the reversed lifted path.  This is the
finite geometric part of orientation reversal; algebraic integrand
certificates remain a separate higher-layer obligation. -/
theorem followedBy_reverse {sheets : Nat} {models : List CellModel}
    {start finish : LiftedPoint sheets} {path : LiftedPath sheets start finish}
    (follows : FollowedBy models path)
    (reversal : CCL.ProgressiveGaussianIntegration.PathModel.ReversalCells
      models) :
    FollowedBy reversal.reversed path.reverse := by
  induction follows with
  | nil point =>
      cases reversal
      exact .nil point
  | @cons start middle finish model models cell remaining start_eq finish_eq
      tail inductionHypothesis =>
      cases reversal with
      | cons head rest =>
          change FollowedBy
            (rest.reversed ++
              [CCL.ProgressiveGaussianIntegration.CellModel.reverse model head])
            (remaining.reverse.append
              (.cons cell.reverse (.nil start)))
          apply followedBy_append (inductionHypothesis rest)
          exact .cons finish_eq start_eq (.nil start)

@[simp] theorem cellCount_reverse {sheets : Nat}
    {start finish : LiftedPoint sheets}
    (path : LiftedPath sheets start finish) :
    path.reverse.cellCount = path.cellCount := by
  induction path with
  | nil point => rfl
  | cons cell remaining inductionHypothesis =>
      rw [reverse, cellCount_append, inductionHypothesis]
      change remaining.cellCount + 1 = remaining.cellCount + 1
      rfl

end LiftedPath

/-- A closed lifted path retains its actual base point and labelled starting
sheet rather than identifying endpoints only propositionally. -/
structure ClosedLiftedPath (sheets : Nat) : Type where
  basepoint : LiftedPoint sheets
  path : LiftedPath sheets basepoint basepoint

namespace ClosedLiftedPath

def cellCount {sheets : Nat} (path : ClosedLiftedPath sheets) : Nat :=
  path.path.cellCount

theorem returns_to_startingSheet {sheets : Nat}
    (path : ClosedLiftedPath sheets) :
    path.path.sheetTransport.forward path.basepoint.sheet =
      path.basepoint.sheet :=
  path.path.sheetTransport_start

end ClosedLiftedPath

/-- Persistent finite refinements of one fixed sheet-aware cycle.  Every call
returns a finite closed lifted path; later calls need not reuse the same
subdivision. -/
structure LiftedCycleRefinement (sheets : Nat) where
  liftedPath : Nat -> ClosedLiftedPath sheets

namespace LiftedCycleRefinement

/-- Reverse every displayed finite representative of a persistent cycle. -/
def reverse {sheets : Nat} (cycle : LiftedCycleRefinement sheets) :
    LiftedCycleRefinement sheets where
  liftedPath := fun index =>
    { basepoint := (cycle.liftedPath index).basepoint
      path := (cycle.liftedPath index).path.reverse }

end LiftedCycleRefinement

/-- A progressive integrand along a sheet-aware cycle.  At every refinement
its displayed integration cells are checked against exactly the cells of the
corresponding finite lift. -/
structure PeriodProgram {sheets : Nat}
    (cycle : LiftedCycleRefinement sheets) where
  integral : RefinementProgram
  follows : forall index,
    LiftedPath.FollowedBy (integral.model index).cells
      (cycle.liftedPath index).path

namespace PeriodProgram

/-- The persistent CCL name of the period represented by this finite
sheet-aware refinement program. -/
def output {sheets : Nat} {cycle : LiftedCycleRefinement sheets}
    (program : PeriodProgram cycle) : CoherentNamed :=
  program.integral.output

/-- Reverse a period program when every displayed quadrature path carries
explicit cellwise reversal data.  This construction deliberately lives at
the geometric `PeriodProgram` layer: reversing the stronger algebraic local
certificates is not inferred from geometry alone. -/
def reverse {sheets : Nat} {cycle : LiftedCycleRefinement sheets}
    (program : PeriodProgram cycle)
    (reversals : forall index,
      CCL.ProgressiveGaussianIntegration.PathModel.Reversal
        (program.integral.model index))
    (aggregate_le : forall index,
      ((program.integral.model index).reverse (reversals index)).aggregateAllowance <=
        CCL.FiniteGeometric.quarterRadius program.integral.errorScale index) :
    PeriodProgram cycle.reverse := by
  let models := CCL.ProgressiveGaussianIntegration.RefinementProgram.ReversalModels.ofPathReversals
    program.integral reversals aggregate_le
  exact
    { integral := program.integral.reverse models
      follows := by
        intro index
        exact LiftedPath.followedBy_reverse (program.follows index)
          (reversals index).cells }

theorem finite_refinement_cellCount {sheets : Nat}
    {cycle : LiftedCycleRefinement sheets} (program : PeriodProgram cycle)
    (index : Nat) :
    (program.integral.model index).cells.length =
      (cycle.liftedPath index).cellCount :=
  LiftedPath.followedBy_length (program.follows index)

/-- Every positive error request is answered by a finite sheet-aware
subdivision whose certified aggregate allowance is below the request. -/
theorem finite_subdivision_accurate {sheets : Nat}
    {cycle : LiftedCycleRefinement sheets} (program : PeriodProgram cycle)
    (current : Nat) (target : CCL.ProgressiveGaussianIntegration.Coordinate)
    (positive : 0 < target) :
    let index := program.integral.approximation.refineIndex current target positive
    (program.integral.model index).aggregateAllowance < target :=
  program.integral.finite_subdivision_accurate current target positive

/-- The period name is productive and its emitted prefix has exact parser
semantics after any requested finite number of bits. -/
theorem output_bitstream_and_error {sheets : Nat}
    {cycle : LiftedCycleRefinement sheets} (program : PeriodProgram cycle)
    (target : CCL.ProgressiveGaussianIntegration.Coordinate)
    (positive : 0 < target)
    (count : Nat) :
    let refined := CCL.TranscendentalOutput.refined
      program.output.name target positive
    (refined.process.ball refined.state).radiusSq < target /\
      refined.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          refined.machine count).emitted /\
      (CCL.ProgressiveTransducer.advance
        refined.machine count).emitted.length = count /\
      CCL.ProgressiveMachineSemantics.ExactCursor
        refined.process refined.state
        (CCL.ProgressiveTransducer.advance refined.machine count) :=
  program.integral.output_bitstream_and_error target positive count

end PeriodProgram

/-- The `2g` common sheet-aware cycle refinements corresponding to a
symplectic homology basis. -/
structure LiftedSymplecticCycles (sheets genus : Nat) where
  aCycle : Fin genus -> LiftedCycleRefinement sheets
  bCycle : Fin genus -> LiftedCycleRefinement sheets

end CCL.Riemann.LiftedPaths
