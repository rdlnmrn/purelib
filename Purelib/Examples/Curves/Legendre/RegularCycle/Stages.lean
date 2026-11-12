module

public import Purelib.Examples.Curves.Legendre.RegularCycle.Primitives
public import Purelib.Examples.Curves.Legendre.RegularCycle.Programs
public import Purelib.Curves.Legendre.Periods.Jets.Source.Stage

/-!
# Admitted primitive stages of the regular cycle

The original four-side model cache consumes one common source request.
Four actual endpoint attachments share their retained points, root readings
and three primitive values between the two incident cells. Each cell's
admission derives its paid comparisons from the original bank and branch
owners. The resulting stage retains the actual ordered source chain.
-/

public section

namespace Purelib.Examples.Curves.Legendre.RegularCycle.Stages

open Purelib.Curves.Legendre.Periods.Jets.Source
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian

/-- The exact original endpoint-plan type with the regular cycle's cached vertex indices fixed. -/
@[expose] def Plans (sheet : Fin 2) (index : Nat) := EndpointPlans (Vertices.build sheet) index

/-- The exact original finite-bank type at the same retained regular-cycle endpoint allocation. -/
@[expose] def Bank {sheet : Fin 2} {index : Nat} (plans : Plans sheet index) :=
  Vertices.Bank (Vertices.build sheet) plans.targets.endpoint

variable {sheet : Fin 2} {cache : Cache (patch sheet)} {floor index : Nat} {target allowance : Rational}
    {request : Request cache floor target}
    {plans : Plans sheet index} {bank : Bank plans}

attribute [local irreducible] patch lowerLeft lowerRight upperRight upperLeft
  Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

set_option genInjectivity false in
/-- The four original source cells and their computed admissions under one actual stage's bank and target cache.

The defining equations retain the original four-side model projections.
The admissions contain the actual shared endpoint attachments and computed
comparisons; reading these fields does not execute another root request.
-/
structure Sides (plans : Plans sheet index) (bank : Bank plans)
    (cells : Cells (sheet := sheet) request allowance) where
  /-- The retained original lower-side source and all its actual primitive models. -/
  lower : Cell (parameter := 2) (lowerSide sheet)
  /-- The lower source consumes the original cached six-channel cell models. -/
  lower_eq : lower = Cell.ofModels request (lowerSide sheet) cells.lower
    (lowerLeft_inside sheet) (lowerRight_inside sheet)
  /-- The retained original right-side source. -/
  right : Cell (parameter := 2) (rightSide sheet)
  /-- The right source consumes the same original common model request. -/
  right_eq : right = Cell.ofModels request (rightSide sheet) cells.right
    (lowerRight_inside sheet) (upperRight_inside sheet)
  /-- The retained original upper-side source. -/
  upper : Cell (parameter := 2) (upperSide sheet)
  /-- The upper source retains its original cell-model cache. -/
  upper_eq : upper = Cell.ofModels request (upperSide sheet) cells.upper
    (upperRight_inside sheet) (upperLeft_inside sheet)
  /-- The retained original left-side source. -/
  left : Cell (parameter := 2) (leftSide sheet)
  /-- The left source retains the same actual common inverse model. -/
  left_eq : left = Cell.ofModels request (leftSide sheet) cells.left
    (upperLeft_inside sheet) (lowerLeft_inside sheet)
  /-- The lower side's internally derived primitive endpoint admission. -/
  lowerAdmission : Cell.Admission lower plans.targets bank.entries
  /-- The right side's computed admission, sharing its endpoint attachments with the adjacent sides. -/
  rightAdmission : Cell.Admission right plans.targets bank.entries
  /-- The upper side's actual primitive admission. -/
  upperAdmission : Cell.Admission upper plans.targets bank.entries
  /-- The left side's actual primitive admission on the same selected sheet. -/
  leftAdmission : Cell.Admission left plans.targets bank.entries
  /-- The actual original stage constructed once from the same prepared bank and admissions. -/
  admitted : Stage 2 (loop sheet) index
  /-- The cached stage consumes exactly the original targets, bank, sources and four admissions. -/
  admitted_eq : admitted = Stage.ofAdmissions plans.targets plans.targets_eq bank.entries bank.lowerLeft
    (.cons lower (.cons right (.cons upper (.cons left (.nil _)))))
    (.cons lowerAdmission (.cons rightAdmission (.cons upperAdmission (.cons leftAdmission (.nil _)))))

namespace Sides

/-- Construct the four actual admissions with one root attachment per original corner.

The source request has already paid the cached maximum of all endpoint
floors. The actual geometric cost fixes its target; local derivative and
endpoint comparisons are derived by the original admission constructor.
-/
def build (plans : Plans sheet index) (bank : Bank plans) (cells : Cells (sheet := sheet) request allowance)
    (cost : Rational) (cost_eq : cost = geometricCost sheet)
    (target_eq : target = plans.targets.sourceTarget cost)
    (paid : plans.stage ≤ request.selection.stage) : Sides plans bank cells := by
  let lower := Cell.ofModels request (lowerSide sheet) cells.lower
    (lowerLeft_inside sheet) (lowerRight_inside sheet)
  let right := Cell.ofModels request (rightSide sheet) cells.right
    (lowerRight_inside sheet) (upperRight_inside sheet)
  let upper := Cell.ofModels request (upperSide sheet) cells.upper
    (upperRight_inside sheet) (upperLeft_inside sheet)
  let left := Cell.ofModels request (leftSide sheet) cells.left
    (upperLeft_inside sheet) (lowerLeft_inside sheet)
  let lowerLeft := plans.lowerLeft.attach request (plans.lowerLeft_stage_le.trans paid)
  let lowerRight := plans.lowerRight.attach request (plans.lowerRight_stage_le.trans paid)
  let upperRight := plans.upperRight.attach request (plans.upperRight_stage_le.trans paid)
  let upperLeft := plans.upperLeft.attach request (plans.upperLeft_stage_le.trans paid)
  have lowerLeftOwner : plans.lowerLeft.requests.bounds.owner.owner = bank.lowerLeft.original.sample.owner :=
    (congrArg (fun sample => sample.owner) plans.lowerLeft.requests.bounds.owner_eq).trans
      (congrArg (fun vertex => vertex.sample.owner) bank.lowerLeft_eq).symm
  have lowerRightOwner : plans.lowerRight.requests.bounds.owner.owner = bank.lowerRight.original.sample.owner :=
    (congrArg (fun sample => sample.owner) plans.lowerRight.requests.bounds.owner_eq).trans
      (congrArg (fun vertex => vertex.sample.owner) bank.lowerRight_eq).symm
  have upperRightOwner : plans.upperRight.requests.bounds.owner.owner = bank.upperRight.original.sample.owner :=
    (congrArg (fun sample => sample.owner) plans.upperRight.requests.bounds.owner_eq).trans
      (congrArg (fun vertex => vertex.sample.owner) bank.upperRight_eq).symm
  have upperLeftOwner : plans.upperLeft.requests.bounds.owner.owner = bank.upperLeft.original.sample.owner :=
    (congrArg (fun sample => sample.owner) plans.upperLeft.requests.bounds.owner_eq).trans
      (congrArg (fun vertex => vertex.sample.owner) bank.upperLeft_eq).symm
  let lowerLeftBranch := plans.lowerLeft.requests.bounds.owner_eq ▸
    RootBranch.ofOwnerEq plans.lowerLeft.requests.bounds.owner bank.lowerLeft.original.sample lowerLeftOwner
  let lowerRightBranch := plans.lowerRight.requests.bounds.owner_eq ▸
    RootBranch.ofOwnerEq plans.lowerRight.requests.bounds.owner bank.lowerRight.original.sample lowerRightOwner
  let upperRightBranch := plans.upperRight.requests.bounds.owner_eq ▸
    RootBranch.ofOwnerEq plans.upperRight.requests.bounds.owner bank.upperRight.original.sample upperRightOwner
  let upperLeftBranch := plans.upperLeft.requests.bounds.owner_eq ▸
    RootBranch.ofOwnerEq plans.upperLeft.requests.bounds.owner bank.upperLeft.original.sample upperLeftOwner
  let lowerStart := Cell.Endpoint.ofAttachment lower bank.lowerLeft plans.lowerLeft lowerLeft lowerLeftBranch
  let lowerFinish := Cell.Endpoint.ofAttachment lower bank.lowerRight plans.lowerRight lowerRight lowerRightBranch
  let rightStart := Cell.Endpoint.ofAttachment right bank.lowerRight plans.lowerRight lowerRight lowerRightBranch
  let rightFinish := Cell.Endpoint.ofAttachment right bank.upperRight plans.upperRight upperRight upperRightBranch
  let upperStart := Cell.Endpoint.ofAttachment upper bank.upperRight plans.upperRight upperRight upperRightBranch
  let upperFinish := Cell.Endpoint.ofAttachment upper bank.upperLeft plans.upperLeft upperLeft upperLeftBranch
  let leftStart := Cell.Endpoint.ofAttachment left bank.upperLeft plans.upperLeft upperLeft upperLeftBranch
  let leftFinish := Cell.Endpoint.ofAttachment left bank.lowerLeft plans.lowerLeft lowerLeft lowerLeftBranch
  have costBounds := geometricCost_bounds sheet
  have lowerCost : lower.primitives.displacementNorm ≤ cost := by
    rewrite [lower.primitives.displacementNorm_eq]
    exact costBounds.1.trans_eq cost_eq.symm
  have rightCost : right.primitives.displacementNorm ≤ cost := by
    rewrite [right.primitives.displacementNorm_eq]
    exact costBounds.2.1.trans_eq cost_eq.symm
  have upperCost : upper.primitives.displacementNorm ≤ cost := by
    rewrite [upper.primitives.displacementNorm_eq]
    exact costBounds.2.2.1.trans_eq cost_eq.symm
  have leftCost : left.primitives.displacementNorm ≤ cost := by
    rewrite [left.primitives.displacementNorm_eq]
    exact costBounds.2.2.2.trans_eq cost_eq.symm
  let lowerAdmission := Cell.Admission.build lower plans.targets bank.entries cost
    lowerCost target_eq lowerStart lowerFinish
  let rightAdmission := Cell.Admission.build right plans.targets bank.entries cost
    rightCost target_eq rightStart rightFinish
  let upperAdmission := Cell.Admission.build upper plans.targets bank.entries cost
    upperCost target_eq upperStart upperFinish
  let leftAdmission := Cell.Admission.build left plans.targets bank.entries cost
    leftCost target_eq leftStart leftFinish
  let sources : Path 2 (loop sheet).path :=
    .cons lower (.cons right (.cons upper (.cons left (.nil _))))
  let admissions : Admissions plans.targets bank.entries sources :=
    .cons lowerAdmission (.cons rightAdmission (.cons upperAdmission (.cons leftAdmission (.nil _))))
  let admitted := Stage.ofAdmissions plans.targets plans.targets_eq bank.entries bank.lowerLeft sources admissions
  exact ⟨lower, rfl, right, rfl, upper, rfl, left, rfl,
    lowerAdmission, rightAdmission, upperAdmission, leftAdmission, admitted, rfl⟩

/-- Read the four original admitted sources in the displayed closed lifted-path order. -/
@[expose] def sources {cells : Cells (sheet := sheet) request allowance} (sides : Sides plans bank cells) :
    Path 2 (loop sheet).path :=
  .cons sides.lower (.cons sides.right (.cons sides.upper (.cons sides.left (.nil _))))

/-- The admitted source chain consumes exactly the original four retained side-model caches. -/
theorem sources_eq {cells : Cells (sheet := sheet) request allowance} (sides : Sides plans bank cells) :
    sides.sources = cells.sourcePath := by
  unfold sources Cells.sourcePath
  rewrite [sides.lower_eq, sides.right_eq, sides.upper_eq, sides.left_eq]
  rfl

/-- Read the four already-computed admissions in that same original path order. -/
@[expose] def admissions {cells : Cells (sheet := sheet) request allowance} (sides : Sides plans bank cells) :
    Admissions plans.targets bank.entries sides.sources :=
  .cons sides.lowerAdmission (.cons sides.rightAdmission
    (.cons sides.upperAdmission (.cons sides.leftAdmission (.nil _))))

/-- Construct the original closed stage from its retained target cache, bank basepoint and admitted actual cells. -/
@[expose] def stage {cells : Cells (sheet := sheet) request allowance} (sides : Sides plans bank cells) :
    Stage 2 (loop sheet) index :=
  sides.admitted

/-- The cached admitted stage retains the literal original six-channel source chain. -/
theorem admitted_sources_eq {cells : Cells (sheet := sheet) request allowance} (sides : Sides plans bank cells) :
    sides.admitted.sources = sides.sources :=
  congrArg (fun original => original.sources) sides.admitted_eq

/-- Recover the same four original admissions under the complete retained stage's actual indices.

The whole original Stage factory equation rules out the other certificate
branch in erased proof. The returned spine is the actual stored inl value;
no source, admission or Stage factory executes to reconstruct that data.
-/
def retainedAdmissions {cells : Cells (sheet := sheet) request allowance} (sides : Sides plans bank cells) :
    Admissions sides.admitted.targets sides.admitted.bank sides.admitted.sources := by
  have legacy : ∃ admitted : Admissions sides.admitted.targets sides.admitted.bank sides.admitted.sources,
      sides.admitted.admissions = Sum.inl admitted :=
    Eq.mp (congrArg (fun actual : Stage 2 (loop sheet) index =>
      ∃ admitted : Admissions actual.targets actual.bank actual.sources,
        actual.admissions = Sum.inl admitted) sides.admitted_eq.symm) ⟨sides.admissions, rfl⟩
  exact match selected : sides.admitted.admissions with
    | .inl admitted => admitted
    | .inr _ => False.elim (by
        rcases legacy with ⟨admitted, expected⟩
        cases selected.symm.trans expected)

/-- The actual lower-right lookup belongs to the retained admitted stage's original bank. -/
@[expose] def admitted_lowerRight {cells : Cells (sheet := sheet) request allowance} (sides : Sides plans bank cells) :
    Vertex.Bank.Found sides.admitted.bank (lowerRight sheet) :=
  sides.admitted_eq.symm ▸ sides.lowerAdmission.finishing.found

/-- The cached admitted stage retains the exact original lower-left primitive vertex. -/
theorem admitted_lowerLeft_original {cells : Cells (sheet := sheet) request allowance}
    (sides : Sides plans bank cells) :
    sides.admitted.base.original = bank.lowerLeft.original :=
  congrArg (fun original => original.base.original) sides.admitted_eq

/-- Transport a retained bank lookup along exact stage equality without changing its original vertex. -/
private theorem original_cast (first second : Stage 2 (loop sheet) index) (equal : first = second)
    (found : Vertex.Bank.Found second.bank (lowerRight sheet)) :
    (equal.symm ▸ found).original = found.original := by
  cases equal
  rfl

/-- The cached lower-right lookup retains the original vertex selected by that same actual finite bank. -/
theorem admitted_lowerRight_original {cells : Cells (sheet := sheet) request allowance}
    (sides : Sides plans bank cells) : sides.admitted_lowerRight.original = bank.lowerRight.original := by
  have same := sides.lowerAdmission.finishing.found.original_eq bank.lowerRight
  unfold admitted_lowerRight
  exact (original_cast _ _ sides.admitted_eq sides.lowerAdmission.finishing.found).trans same

/-- The closed admitted stage retains the literal original six-channel source chain. -/
theorem stage_sources_eq {cells : Cells (sheet := sheet) request allowance} (sides : Sides plans bank cells) :
    sides.stage.sources = cells.sourcePath := sides.admitted_sources_eq.trans sides.sources_eq

end Sides

end Purelib.Examples.Curves.Legendre.RegularCycle.Stages

end
