#!/usr/bin/env python3
"""Produce untrusted ordered triangle-sewing trees for exact Lean replay.

Input: {"vertex_count": N, "faces": [[a,b,c], ...]}.
The first available reverse edge between two patches is sewn.  Other matching
occurrences remain cuts.  No geometric, root-transport, or A/B-basis claim is
made by this producer.  Lean checks seam orientation, complete face coverage,
maximality, and the generic sewing invariants independently.
"""

import argparse
from collections import deque
import json
from pathlib import Path



from scripts.generators.lean_layout import format_lean


def read_mesh(path):
    mesh = json.loads(path.read_text())
    count = mesh["vertex_count"]
    faces = mesh["faces"]
    if type(count) is not int or count < 0:
        raise ValueError("vertex_count must be a nonnegative integer")
    if not isinstance(faces, list):
        raise ValueError("faces must be a list")
    for face in faces:
        if not isinstance(face, list) or len(face) != 3:
            raise ValueError("every face must have three vertex indices")
        if any(type(index) is not int or not 0 <= index < count for index in face):
            raise ValueError("face vertex outside the declared vertex bank")
    return count, faces


def forest(faces, *, right_nested=False):
    patches = []
    for index, (a, b, c) in enumerate(faces):
        patches.append({"tree": (index,), "boundary": [(a, b), (b, c), (c, a)]})
    while True:
        found = None
        for first in range(len(patches)):
            for second in range(first + 1, len(patches)):
                left, right = patches[first]["boundary"], patches[second]["boundary"]
                for i, (a, b) in enumerate(left):
                    for j, edge in enumerate(right):
                        if edge == (b, a):
                            found = first, second, i, j
                            break
                    if found is not None:
                        break
                if found is not None:
                    break
            if found is not None:
                break
        if found is None:
            return patches
        first, second, i, j = found
        left, right = patches[first], patches[second]
        if right_nested:
            left, right, i, j = right, left, j, i
        patches[first] = {
            "tree": (left["tree"], right["tree"], i, j),
            "boundary": left["boundary"][i + 1:] + left["boundary"][:i]
            + right["boundary"][j + 1:] + right["boundary"][:j],
        }
        del patches[second]


def lean_tree(tree):
    if len(tree) == 1:
        return f"(.leaf ⟨{tree[0]}, by decide⟩)"
    left, right, i, j = tree
    return f"(.join {lean_tree(left)} {lean_tree(right)} {i} {j})"


def sewing_shape(tree):
    """Geometry-only [right depth, charge factor, faces, total amplification]."""
    if len(tree) == 1:
        return [0, 0, 1, 0]
    left, right = sewing_shape(tree[0]), sewing_shape(tree[1])
    depth = max(left[0], right[0] + 1)
    factor = (16 * left[0] + 1) * left[1] + (16 * right[0] + 1) * right[1] + 2
    faces = left[2] + right[2]
    return [depth, factor, faces, 2 * faces * depth * factor]


def primitive_boundary_reading(sample, edge, local_values):
    start, finish = edge
    for position, trace in enumerate(sample["faces"]):
        triangle = trace["triangle"]
        for first in range(3):
            last = (first + 1) % 3
            if (triangle[first], triangle[last]) == edge:
                local = local_values[trace["source"]]
                increment = local[last] - local[first]
                error = sample["values"][finish] - sample["values"][start] - increment
                allowance = 4 * trace["allowance"]
                if error * error > allowance:
                    raise ValueError("boundary owner lost an inherited face error")
                return [start, finish, position, trace["source"], first, last, increment, error, allowance]
    raise ValueError("sewn boundary edge has no actual triangle owner")


def primitive_assembly(faces, tree, local_values):
    """Independently replay cut-vertex sewing and exact integer primitives.

    Local values are untrusted regression data. Only the displayed seam
    endpoints are identified; unused cut-bank slots remain present.
    """
    if len(local_values) != len(faces) or any(len(row) != 3 or any(type(value) is not int for value in row)
                                             for row in local_values):
        raise ValueError("primitive data need three exact integers per face")

    def replay(node):
        if len(node) == 1:
            index = node[0]
            if type(index) is not int or not 0 <= index < len(faces):
                raise ValueError("primitive leaf outside the face bank")
            return {"labels": list(faces[index]), "boundary": [(0, 1), (1, 2), (2, 0)],
                    "values": list(local_values[index]), "charges": [], "mismatches": [], "contacts": [],
                    "faces": [{"source": index, "triangle": [0, 1, 2], "errors": [0, 0, 0],
                               "terms": [[], [], []], "depth": 0, "charge": 0, "allowance": 0}]}
        if len(node) != 4:
            raise ValueError("invalid primitive assembly node")
        first, second, i, j = node
        left, right = replay(first), replay(second)
        if type(i) is not int or type(j) is not int or not 0 <= i < len(left["boundary"]) or not 0 <= j < len(right["boundary"]):
            raise ValueError("primitive seam position outside the boundary")
        a, b = left["boundary"][i]
        c, d = right["boundary"][j]
        if a == b or c == d:
            raise ValueError("primitive seam endpoints must be distinct")
        if (left["labels"][a], left["labels"][b]) != (right["labels"][d], right["labels"][c]):
            raise ValueError("primitive seam has inconsistent orientation")
        shift = left["values"][b] - right["values"][c]
        defect = left["values"][a] - right["values"][d] - shift
        left_reading = primitive_boundary_reading(left, (a, b), local_values)
        right_reading = primitive_boundary_reading(right, (c, d), local_values)
        mismatch = (left_reading[6] + right_reading[6]) ** 2
        if defect * defect > 4 * (left_reading[8] + right_reading[8]) + 2 * mismatch:
            raise ValueError("seam charge exceeds inherited errors plus original local mismatch")
        left_count = len(left["values"])

        def vertex(index):
            return b if index == c else a if index == d else left_count + index

        boundary = left["boundary"][i + 1:] + left["boundary"][:i]
        boundary += [(vertex(x), vertex(y)) for x, y in right["boundary"][j + 1:] + right["boundary"][:j]]
        traces = list(left["faces"])
        for trace in right["faces"]:
            corrections = [(defect if index == d else 0) - (defect if trace["triangle"][0] == d else 0)
                           for index in trace["triangle"]]
            depth, charge = trace["depth"] + 1, trace["charge"] + defect * defect
            traces.append({"source": trace["source"], "triangle": [vertex(index) for index in trace["triangle"]],
                           "errors": [new + old for new, old in zip(corrections, trace["errors"])],
                           "terms": [[new] + old for new, old in zip(corrections, trace["terms"])],
                           "depth": depth, "charge": charge, "allowance": depth * charge})
        return {"labels": left["labels"] + right["labels"], "boundary": boundary,
                "values": left["values"] + [value + shift for value in right["values"]],
                "charges": [defect * defect] + left["charges"] + right["charges"], "faces": traces,
                "mismatches": [mismatch] + left["mismatches"] + right["mismatches"],
                "contacts": [[*left_reading[3:6], *right_reading[3:6], mismatch]] + left["contacts"] + right["contacts"]}

    sample = replay(tree)
    for trace in sample["faces"]:
        local = local_values[trace["source"]]
        actual = [sample["values"][index] for index in trace["triangle"]]
        if trace["errors"] != [actual[i] - actual[0] - (local[i] - local[0]) for i in range(3)]:
            raise ValueError("primitive face trace disagrees with actual sewn increments")
        for error, terms in zip(trace["errors"], trace["terms"]):
            if error != sum(terms) or len(terms) > trace["depth"] or sum(x * x for x in terms) > trace["charge"]:
                raise ValueError("primitive face trace has an invalid seam decomposition")
            if error * error > trace["allowance"]:
                raise ValueError("primitive face error exceeds its finite trace allowance")
    sample["total_allowance"] = sum(trace["allowance"] for trace in sample["faces"])
    sample["squared_errors"] = sum(sum(error * error for error in trace["errors"][1:]) for trace in sample["faces"])
    if sample["squared_errors"] > 2 * sample["total_allowance"]:
        raise ValueError("primitive assembly exceeds its whole-face error allowance")
    sample["boundary_readings"] = [primitive_boundary_reading(sample, edge, local_values) for edge in sample["boundary"]]
    sample["shape"] = sewing_shape(tree)
    depth, factor, face_count, amplification = sample["shape"]
    total_charge = sum(sample["charges"])
    maximum_mismatch = max(sample["mismatches"], default=0)
    if total_charge > factor * maximum_mismatch:
        raise ValueError("sewn charges exceed geometry-only amplification of local mismatches")
    if sample["squared_errors"] > 2 * face_count * depth * total_charge:
        raise ValueError("whole-face errors exceed their depth and charge accounting")
    if sample["squared_errors"] > amplification * maximum_mismatch:
        raise ValueError("whole-tree error bound lost depth, face count or inherited errors")
    return sample


def cancellation_counts(patches):
    remaining = [edge for patch in patches for edge in patch["boundary"]]
    pairs = external = 0
    while remaining:
        a, b = remaining.pop(0)
        if (b, a) in remaining:
            remaining.remove((b, a))
            pairs += 1
        else:
            external += 1
    return pairs, external


def boundary_word(boundary):
    """Residual generators first, then first occurrences of retained pairs.

    Positions, rather than edge equality, identify occurrences. The final
    signed, one-based word preserves the supplied cyclic boundary order.
    This produces regression data, not a geometric intersection certificate.
    """
    remaining = list(range(len(boundary)))
    residual, pairs = [], []
    while remaining:
        first = remaining.pop(0)
        a, b = boundary[first]
        opposite = next((index for index in remaining if boundary[index] == (b, a)), None)
        if opposite is None:
            residual.append(first)
        else:
            remaining.remove(opposite)
            pairs.append((first, opposite))
    generators = [boundary[index] for index in residual] + [boundary[first] for first, _ in pairs]
    word = [0] * len(boundary)
    for generator, index in enumerate(residual, 1):
        word[index] = generator
    for generator, (first, opposite) in enumerate(pairs, len(residual) + 1):
        word[first], word[opposite] = generator, -generator
    return generators, word


def word_signature(count, word):
    """Independent prefix scan; Lean's specification uses ordered suffixes.

    Coefficients measure doubled area, not a presumed symplectic form.
    """
    total = [0] * count
    matrix = [[0] * count for _ in range(count)]
    for letter in word:
        if type(letter) is not int or not 1 <= abs(letter) <= count:
            raise ValueError("signed generator outside the declared alphabet")
        index, sign = abs(letter) - 1, 1 if letter > 0 else -1
        for other in range(count):
            matrix[other][index] += total[other] * sign
            matrix[index][other] -= sign * total[other]
        total[index] += sign
    return total, matrix


def integral_pairing(one_sided, matrix):
    """Retain the entire boundary remainder, including mixed interactions.

    This untrusted producer rejects an odd paired coefficient; Lean proves
    integrality from signed occurrence counts for every extracted cut word.
    """
    count = len(one_sided)
    if len(matrix) != count or any(len(row) != count for row in matrix):
        raise ValueError("pairing matrix dimensions differ from the alphabet")
    paired = [[0] * count for _ in range(count)]
    remaining = [[0] * count for _ in range(count)]
    for row in range(count):
        for column in range(count):
            value = matrix[row][column]
            if not one_sided[row] and not one_sided[column]:
                if value % 2:
                    raise ValueError("odd area coefficient on paired generators")
                paired[row][column] = value // 2
            remaining[row][column] = value - 2 * paired[row][column]
    return paired, remaining


def chord_intervals(one_sided, word):
    """Retain exact cyclic positions, including both endpoint occurrences.

    The returned finite rows independently predict the Lean chord caches.
    One-sided letters remain in each interval and its physical total.
    """
    if any(type(flag) is not bool for flag in one_sided):
        raise ValueError("one-sided mask must contain booleans")
    count = len(one_sided)
    word_signature(count, word)  # Validate signed indices, including bool rejection.
    for index, side in enumerate(one_sided, 1):
        if word.count(index) != 1 or word.count(-index) != (0 if side else 1):
            raise ValueError("chord word does not have the declared signed multiplicities")
    chords = []
    for index, side in enumerate(one_sided):
        if side:
            continue
        first = word.index(index + 1)
        rotated = word[first:] + word[:first]
        last = rotated.index(-index - 1)
        inside = rotated[1:last]
        total, _ = word_signature(count, inside)
        chords.append({"index": index, "first": first, "inside_length": last - 1,
                       "interval": rotated[:last + 1],
                       "paired": [0 if boundary else value for boundary, value in zip(one_sided, total)],
                       "physical": [value if boundary else 0 for boundary, value in zip(one_sided, total)]})
    return chords


def unit_pivot_reduction(matrix):
    """Produce a deterministic disjoint unit-pivot plan, not a basis theorem.

    The full residual matrix is retained if this restricted algorithm stops
    before normal form. Such a stop says nothing about other integral basis
    algorithms. Lean replays every submitted step and checks the final form.
    """
    count = len(matrix)
    if any(len(row) != count for row in matrix):
        raise ValueError("unit reduction requires a square matrix")
    if any(type(matrix[i][j]) is not int or matrix[i][j] != -matrix[j][i]
           for i in range(count) for j in range(count)):
        raise ValueError("unit reduction requires an alternating integer matrix")
    current = [row[:] for row in matrix]
    available = list(range(count))
    pivots, stages = [], []
    while True:
        pivot = next(((i, j) for i in available for j in available if current[i][j] == 1), None)
        if pivot is None:
            unresolved = [(i, j, current[i][j]) for i in available for j in available if current[i][j] != 0]
            return {"pivots": pivots, "stages": stages, "matrix": current,
                    "available": available, "unresolved": unresolved,
                    "status": "inconclusive-no-unit" if unresolved else "normal-form"}
        first, last = pivot
        left = [0 if i in pivot else -current[i][last] for i in range(count)]
        right = [0 if i in pivot else current[i][first] for i in range(count)]
        # Deliberately compute by row then column operations, independently
        # of Lean's expanded nine-term entry formula.
        rows = [[current[i][j] + left[i] * current[first][j] + right[i] * current[last][j]
                 for j in range(count)] for i in range(count)]
        current = [[rows[i][j] + left[j] * rows[i][first] + right[j] * rows[i][last]
                    for j in range(count)] for i in range(count)]
        pivots.append(pivot)
        stages.append({"left": left, "right": right, "matrix": current})
        available = [i for i in available if i not in pivot]


def dual_values(reduction, values, *, backward=False):
    """Apply inverse-transpose shears; undo them in reverse order if asked.

    These are pairing arguments, not the ordinary basis-coordinate changes.
    Every weighted sum consumes the original values at its own stage.
    """
    if len(values) != len(reduction["matrix"]) or any(type(value) is not int for value in values):
        raise ValueError("dual evaluation requires one integer value per matrix coordinate")
    current = values[:]
    stages = list(zip(reduction["pivots"], reduction["stages"]))
    if backward:
        stages.reverse()
    for (first, last), stage in stages:
        left_total = sum(weight * value for weight, value in zip(stage["left"], current))
        right_total = sum(weight * value for weight, value in zip(stage["right"], current))
        current[first] += left_total if backward else -left_total
        current[last] += right_total if backward else -right_total
    return current


def cycle_rows(reduction):
    """Compute ordinary integer cycle rows by direct chronological shears.

    Lean independently obtains each row by applying the inverse dual map
    to its coordinate unit vector. The two computations must agree.
    """
    count = len(reduction["matrix"])
    rows = [[int(i == j) for j in range(count)] for i in range(count)]
    for (first, last), stage in zip(reduction["pivots"], reduction["stages"]):
        rows = [[rows[i][j] + stage["left"][i] * rows[first][j] + stage["right"][i] * rows[last][j]
                 for j in range(count)] for i in range(count)]
    return rows


def weighted_period_rows(rows, real_values, imaginary_values, error_bounds):
    """Independent exact samples and Cauchy charges for integer cycle rows.

    No polynomial/root integration is performed here. These data check the
    downstream weighting of already certified component periods.
    """
    count = len(real_values)
    if len(imaginary_values) != count or len(error_bounds) != count:
        raise ValueError("weighted period data require equal component counts")
    if any(type(value) is not int for values in (real_values, imaginary_values, error_bounds) for value in values):
        raise ValueError("weighted period fixtures require exact integer data")
    if any(bound < 0 for bound in error_bounds):
        raise ValueError("squared-error bounds must be nonnegative")
    result = []
    for row in rows:
        if len(row) != count or any(type(weight) is not int for weight in row):
            raise ValueError("each integer cycle row must have one weight per component")
        result.append({
            "sample": (sum(w * v for w, v in zip(row, real_values)),
                       sum(w * v for w, v in zip(row, imaginary_values))),
            "mass": count * sum(w * w for w in row),
            "charge": count * sum(w * w * e for w, e in zip(row, error_bounds)),
        })
    return result


def interlaced_surgery(word, first, last):
    """Rotate to +p and reconnect p U q V -p W -q X as U X W V."""
    if type(first) is not int or type(last) is not int or min(first, last) < 0 or first == last:
        raise ValueError("surgery requires two distinct nonnegative generator indices")
    p, q = first + 1, last + 1
    if any(word.count(letter) != 1 for letter in (p, q, -p, -q)):
        raise ValueError("surgery pivot orientations must occur exactly once")
    rotation = word.index(p)
    before = word[rotation:] + word[:rotation]
    q_at, minus_p_at, minus_q_at = (before.index(letter) for letter in (q, -p, -q))
    if not 0 < q_at < minus_p_at < minus_q_at:
        raise ValueError("the supplied oriented pair does not interlace positively")
    u, v = before[1:q_at], before[q_at + 1:minus_p_at]
    w, x = before[minus_p_at + 1:minus_q_at], before[minus_q_at + 1:]
    return {"first": first, "last": last, "rotation": rotation, "before": before,
            "u": u, "v": v, "w": w, "x": x, "after": u + x + w + v}


def word_surgeries(count, word, pivots):
    """Retain the literal word at every submitted matrix-pivot step."""
    total, _ = word_signature(count, word)
    if any(total) or len(set(word)) != len(word):
        raise ValueError("handle surgery requires a balanced unique signed word")
    steps = []
    handles = [[0] * count for _ in range(count)]
    current = word[:]
    for first, last in pivots:
        step = interlaced_surgery(current, first, last)
        step["source_matrix"] = word_signature(count, step["before"])[1]
        current = step["after"]
        next_total, next_matrix = word_signature(count, current)
        if any(next_total) or len(set(current)) != len(current):
            raise ValueError("word reconnection failed its occurrence invariant")
        handles[first][last], handles[last][first] = 2, -2
        step["residual_matrix"] = next_matrix
        step["split_matrix"] = [[handles[i][j] + next_matrix[i][j] for j in range(count)] for i in range(count)]
        steps.append(step)
    return steps


def lean_letters(word):
    return "[" + ", ".join(f"⟨⟨{abs(letter) - 1}, by decide⟩, {'true' if letter < 0 else 'false'}⟩" for letter in word) + "]"


def lean_surgeries(count, steps):
    result = []
    previous = "pairedLetters"
    for index, step in enumerate(steps):
        name = f"wordSurgery{index}"
        result.append(f'''
def {name} : InterlacedWord cutWord.alphabet.count :=
  show InterlacedWord {count} from
    {{ first := ⟨{step['first']}, by decide⟩
      last := ⟨{step['last']}, by decide⟩
      distinct := by decide
      u := {lean_letters(step['u'])}
      v := {lean_letters(step['v'])}
      w := {lean_letters(step['w'])}
      x := {lean_letters(step['x'])} }}
theorem {name}_rotation : {name}.before = {previous}.drop {step['rotation']} ++ {previous}.take {step['rotation']} := by decide
theorem {name}_counts (index : Fin cutWord.alphabet.count) (reversed : Bool) :
    Purelib.Topology.Surface.Word.SignedWord.SignedGenerator.occurrences ⟨index, reversed⟩ {name}.before ≤ 1 := by decide +revert
theorem {name}_closed (index : Fin cutWord.alphabet.count) :
    Purelib.Topology.Surface.Word.Pairing.totalAt ({name}.before.map Purelib.Topology.Surface.Word.SignedWord.SignedGenerator.coefficients) index = 0 := by decide +revert
def {name}Source := Purelib.Topology.Surface.Word.Surgery.IntegralWordSignature.build (Purelib.Topology.Surface.Word.Pairing.Signature.build ({name}.before.map Purelib.Topology.Surface.Word.SignedWord.SignedGenerator.coefficients)) {name}_closed
def {name}Reduced := ({name}.unitPivot {name}Source {name}_counts).reduced
def {name}Target := Purelib.Topology.Surface.Word.NormalForm.InterlacedWord.afterIntegral {name} {name}Source {name}_counts {name}_closed {name}Reduced (fun _ _ => rfl)
def {name}Selected := selectWord {name}.before {name}Source {name}_counts {name}_closed
def {name}Normal := normalizeWord {name}.before {name}Source {name}_counts {name}_closed
example (row column : Fin cutWord.alphabet.count) :
    ({name}.unitPivot {name}Source {name}_counts).reduced row column =
      Purelib.LinearAlgebra.Alternating.Handle.Basic.handleEntry [({name}.first, {name}.last)] row column + {name}Target.matrix row column :=
  {name}.reduced_eq_handle_add {name}Source {name}Target {name}_counts {name}_closed row column
example (index : Fin cutWord.alphabet.count) (reversed : Bool) :
    Purelib.Topology.Surface.Word.SignedWord.SignedGenerator.occurrences ⟨index, reversed⟩ {name}.after ≤ 1 := {name}.after_counts_le {name}_counts index reversed
example : {name}.after.length + 4 = {name}.before.length := {name}.after_length
''')
        previous = f"{name}.after"
    return "".join(result)


def lean_surgery_checks(steps):
    return "".join(f'''  let surgerySource{index} := indices.map fun row => indices.map fun column => wordSurgery{index}Source.signature.matrix row column
  let surgeryTarget{index} := indices.map fun row => indices.map fun column => wordSurgery{index}Target.signature.matrix row column
  unless surgerySource{index} == ({step['source_matrix']} : List (List Int)) &&
      surgeryTarget{index} == ({step['residual_matrix']} : List (List Int)) do
    throw (IO.userError "literal word surgery differs from independently generated signatures")
  unless indices.all (fun row => indices.all (fun column => wordSurgery{index}Reduced row column ==
      Purelib.LinearAlgebra.Alternating.Handle.Basic.handleEntry [(wordSurgery{index}.first, wordSurgery{index}.last)] row column +
        wordSurgery{index}Target.matrix row column)) do
    throw (IO.userError "literal word reconnection differs from the exact integer pivot")
  match wordSurgery{index}Selected with
  | .zero _ => throw (IO.userError "automatic selection discarded a generated unit handle")
  | .handle selected =>
      unless decide (selected.cut.first = wordSurgery{index}.first ∧ selected.cut.last = wordSurgery{index}.last) &&
          decide (selected.cut.u = wordSurgery{index}.u ∧ selected.cut.v = wordSurgery{index}.v ∧
            selected.cut.w = wordSurgery{index}.w ∧ selected.cut.x = wordSurgery{index}.x) do
        throw (IO.userError "automatic interlacing differs from the independently generated literal segments")
  let normalPivots{index} := wordSurgery{index}Normal.pivots.map fun pair => (pair.1.val, pair.2.val)
  unless normalPivots{index} == {[(entry['first'], entry['last']) for entry in steps[index:]]} &&
      decide (wordSurgery{index}Normal.trace.terminalWord = wordSurgery{len(steps) - 1}.after) do
    throw (IO.userError "automatic normalization differs from the generated full pivot plan or terminal word")
  unless indices.all (fun row => indices.all fun column => wordSurgery{index}Normal.normal.reduction.output row column ==
      Purelib.LinearAlgebra.Alternating.Handle.Basic.handleEntry wordSurgery{index}Normal.pivots row column) do
    throw (IO.userError "automatic normalization lost a previously extracted handle")
''' for index, step in enumerate(steps))


def dual_paths(faces):
    """Deterministic breadth-first paths, retaining both edge positions."""
    if not faces:
        return None
    boundaries = [[(a, b), (b, c), (c, a)] for a, b, c in faces]
    occurrences = {}
    for face, boundary in enumerate(boundaries):
        for position, edge in enumerate(boundary):
            occurrences.setdefault(edge, []).append((face, position))
    paths = [None] * len(faces)
    paths[0] = []
    pending = deque([0])
    while pending:
        first = pending.popleft()
        for first_position, (a, b) in enumerate(boundaries[first]):
            for following, next_position in occurrences.get((b, a), []):
                if paths[following] is None:
                    paths[following] = paths[first] + [(following, first_position, next_position)]
                    pending.append(following)
    return paths if all(path is not None for path in paths) else None


def oriented_unique(faces):
    edges = [edge for a, b, c in faces for edge in [(a, b), (b, c), (c, a)]]
    return len(edges) == len(set(edges))


def lean_energy_area_checks():
    """Exercise conjugate energy data on the same retained geometric caches.

    The perturbed rows deliberately subtract the already measured cut defects;
    this isolates area transfer, not acquisition of actual curve periods (the
    generic grid client checks that bridge). Physical corrections are retained.
    All numerical choices live here; Lean verifies the resulting inequalities.
    """
    return '''  do
    let energyPrimitive := fun index => Purelib.Integration.Energy.Polygon.energyPrimitivePoint (primitive index).right
    let energyWord := Purelib.Topology.Surface.Cut.WordArea.CutBoundaryWord.AreaSample.build word energyPrimitive (energyPrimitive polygon.patch.cut.anchor)
    let energyBank := cycleRoutes.sample integral energyPrimitive energyWord.values
    let energyCycles := Purelib.Topology.Surface.Sewing.NormalFormCycles.build normal.normal energyBank
    let energyEvaluated := Purelib.Topology.Surface.Boundary.NormalFormArea.build normal.normal energyWord.values
    let dual := Purelib.Topology.Surface.Boundary.DualCoordinateBounds.DualMagnitude.build normal.normal.reduction
    let endpointBound := (List.finRange polygon.patch.cut.count).foldl
      (fun bound index => max bound (Purelib.Data.Gaussian.Norm.Basic.normSq (energyPrimitive index).right)) 0
    if endpointNonnegative : 0 ≤ endpointBound then
      if endpoints : ∀ edge ∈ polygon.patch.cut.boundary,
          Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (energyPrimitive edge.start) endpointBound ∧ Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (energyPrimitive edge.finish) endpointBound then
        have inputBound := Purelib.Topology.Surface.Cut.GeneratorBounds.CutBoundaryWord.AreaSample.values_bounded energyWord pairing rfl endpoints
        have inputNonnegative : 0 ≤ 4 * endpointBound :=
          Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) endpointNonnegative
        let magnitude := dual.factor * (4 * endpointBound)
        have magnitudeNonnegative : 0 ≤ magnitude := Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct dual.positive.le inputNonnegative
        have bounded := Purelib.Topology.Surface.Word.NormalFormMagnitude.NormalFormArea.bounded energyEvaluated dual inputNonnegative inputBound
        have conjugate := Purelib.Topology.Surface.Word.NormalFormMagnitude.NormalFormArea.conjugate energyEvaluated (Purelib.Topology.Surface.Cut.GeneratorBounds.CutBoundaryWord.AreaSample.values_conjugate energyWord (fun _ => rfl))
        for index in List.finRange word.alphabet.count do
          unless decide (Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (energyEvaluated.points index) magnitude ∧
              (energyEvaluated.points index).left = Purelib.Data.Gaussian.Basic.conj (energyEvaluated.points index).right) do
            throw (IO.userError "cached dual amplification or conjugacy failed on the actual retained generators")
        for target in ([1, 1 / 1024] : List Purelib.Riemann.Periods.WeightedPeriods.Coordinate) do
          if positive : 0 < target then
            let budget := Purelib.Topology.Surface.Boundary.HandleAreaBudgets.HandleAreaBudget.build magnitude magnitudeNonnegative normal.pivots.length target positive
            let epsilon := budget.rowTarget / (4 * (Purelib.Approximation.Rational.Budget.Aggregate.countCoordinate word.alphabet.count + 1))
            let perturbation := fun index : Fin word.alphabet.count =>
              (⟨epsilon, Purelib.Approximation.Rational.Budget.Aggregate.countCoordinate (index.val + 1) * epsilon⟩ : Gaussian)
            let energyRows := Purelib.Data.Vector.Basic.vectorOfFn fun index =>
              (energyCycles.jumps index).right - (energyCycles.errors index).right + perturbation index
            let corrected := Purelib.Riemann.Periods.CorrectedPeriodArea.build energyCycles energyRows
            if firstBound : ∀ pair ∈ normal.pivots, Purelib.Data.Gaussian.Norm.Basic.normSq
                (-energyRows pair.2 - ((energyEvaluated.points pair.1).right - (energyCycles.physical pair.2).right)) ≤ budget.rowTarget then
              if lastBound : ∀ pair ∈ normal.pivots, Purelib.Data.Gaussian.Norm.Basic.normSq
                  (energyRows pair.1 - ((energyEvaluated.points pair.2).right + (energyCycles.physical pair.1).right)) ≤ budget.rowTarget then
                have accurate := corrected.accurate energyEvaluated budget bounded conjugate firstBound lastBound
                let remainder := Purelib.Topology.Surface.Word.Pairing.contract (fun row column => integral.remaining row column) energyWord.values
                let referenceArea := 2 * energyEvaluated.area + remainder
                have boundary : Purelib.Data.Gaussian.Norm.Basic.normSq
                    (referenceArea - (2 * energyEvaluated.area + remainder)) < budget.boundaryTarget := by
                  rw [Purelib.Data.Gaussian.Basic.sub_self, Purelib.Data.Gaussian.Norm.Basic.normSq_zero]
                  exact budget.boundary_positive
                have _combined := budget.combine referenceArea energyEvaluated.area corrected.area remainder boundary accurate
                unless decide (0 < epsilon ∧ Purelib.Data.Gaussian.Norm.Basic.normSq (corrected.area - energyEvaluated.area) < budget.handleTarget ∧
                    Purelib.Data.Gaussian.Norm.Basic.normSq (referenceArea - (2 * corrected.area + remainder)) < target) do
                  throw (IO.userError ("quadratic period-area transfer lost its perturbation product, " ++
                    "handle count or physical remainder"))
                for pair in normal.pivots do
                  have _firstReadback := corrected.first_eq_energy pair
                  have _lastReadback := corrected.last_eq_energy pair
                  unless edgeArea ((corrected.first pair).sub (energyEvaluated.points pair.1))
                      ((corrected.last pair).sub (energyEvaluated.points pair.2)) != 0 do
                    throw (IO.userError "the area regression did not exercise the product of both perturbations")
                  unless (corrected.first pair).right == -energyRows pair.2 + (energyCycles.physical pair.2).right &&
                      (corrected.last pair).right == energyRows pair.1 - (energyCycles.physical pair.1).right do
                    throw (IO.userError "the area cache changed a handle orientation or discarded its physical row")
              else throw (IO.userError "the generated last-row perturbation exceeds its requested tolerance")
            else throw (IO.userError "the generated first-row perturbation exceeds its requested tolerance")
          else throw (IO.userError "the energy area regression target must be positive")
        profileLog profile "pairing: conjugate energy area and cached magnitudes checked at two requested precisions"
      else throw (IO.userError "energy endpoints escaped their exact finite maximum")
    else throw (IO.userError "the energy endpoint maximum is negative")
'''


def render(count, faces, patches):
    data = ".nil"
    for a, b, c in reversed(faces):
        triangle = f"⟨⟨{a}, by decide⟩, ⟨{b}, by decide⟩, ⟨{c}, by decide⟩⟩"
        data = f".cons {triangle} ({data})"
    trees = ",\n  ".join(lean_tree(patch["tree"]) for patch in patches)
    local_primitives = [[11 * face + corner * corner + 2 * corner - 7 for corner in range(3)]
                        for face in range(len(faces))]
    primitive_data = ".nil"
    for row in reversed(local_primitives):
        values = ".nil"
        for value in reversed(row):
            values = f".cons ⟨Purelib.Data.Rat.Fraction.Cast.fromInt ({value}), 0⟩ ({values})"
        primitive_data = f".cons ({values}) ({primitive_data})"
    primitive_samples = [primitive_assembly(faces, patch["tree"], local_primitives) for patch in patches]
    right_patches = forest(faces, right_nested=True)
    right_trees = ",\n  ".join(lean_tree(patch["tree"]) for patch in right_patches)
    primitive_samples += [primitive_assembly(faces, patch["tree"], local_primitives) for patch in right_patches]
    primitive_values = [sample["values"] for sample in primitive_samples]
    primitive_charges = [sample["charges"] for sample in primitive_samples]
    primitive_faces = [[[trace["source"], *trace["triangle"], *trace["errors"], trace["depth"], trace["charge"], trace["allowance"]]
                        for trace in sample["faces"]] for sample in primitive_samples]
    primitive_totals = [[sample["total_allowance"], sample["squared_errors"], sum(sample["charges"]), *sample["shape"]] for sample in primitive_samples]
    primitive_boundaries = [sample["boundary_readings"] for sample in primitive_samples]
    primitive_contacts = [sample["contacts"] for sample in primitive_samples]
    boundary_count = sum(len(patch["boundary"]) for patch in patches)
    cut_pairs, exterior_count = cancellation_counts(patches)
    connection = ""
    connection_check = ""
    paths = dual_paths(faces)
    if paths is not None and oriented_unique(faces):
        path_data = ".nil"
        for path in reversed(paths):
            steps = ", ".join(f"⟨⟨{following}, by decide⟩, {first_pos}, {next_pos}⟩" for following, first_pos, next_pos in path)
            path_data = f".cons [{steps}] ({path_data})"
        connection = f'''
def dualPathData : Purelib.Data.Vector (List (DualStep faceCount)) faceCount :=
  {path_data}
def connection : DualConnection faces := (Purelib.Topology.Mesh.Replay.DualReplay.DualConnection.checkPaths faces ⟨0, by decide⟩ dualPathData).toOption.get (by decide)
def singlePolygon : SinglePolygon certified := Purelib.Topology.Surface.Sewing.SewingConnected.SewingForest.singlePolygon certified (by decide) connection

example : singlePolygon.patch.faceIndices.length = faceCount := singlePolygon.face_count
example : singlePolygon.patch.cut.boundary.length = faceCount + 2 := singlePolygon.boundaryCount
'''
        connection_check = '''  let connectedAutomatic := Purelib.Topology.Surface.Sewing.SewingConnected.SewingForest.singlePolygon automatic (by decide) connection
  unless connectedAutomatic.patch.faceIndices.length == faceCount do
    throw (IO.userError "dual connectivity failed to produce one complete polygon")
'''
        if all(len(set(face)) == 3 for face in faces):
            generators, signed_word = boundary_word(patches[0]["boundary"])
            word_total, word_matrix = word_signature(len(generators), signed_word)
            one_sided = [value != 0 for value in word_total]
            paired_matrix, remaining_matrix = integral_pairing(one_sided, word_matrix)
            chords = chord_intervals(one_sided, signed_word)
            chord_data = "[" + ", ".join(
                f"({chord['index']}, {chord['first']}, {chord['inside_length']}, {chord['interval']})"
                for chord in chords) + "]"
            reduction = unit_pivot_reduction(paired_matrix)
            paired_word = [letter for letter in signed_word if not one_sided[abs(letter) - 1]]
            surgeries = word_surgeries(len(generators), paired_word, reduction["pivots"])
            for surgery, stage in zip(surgeries, reduction["stages"]):
                if surgery["split_matrix"] != [[2 * entry for entry in row] for row in stage["matrix"]]:
                    raise ValueError("word surgery and matrix reduction disagree")
            pivot_data = "[" + ", ".join(f"(⟨{i}, by decide⟩, ⟨{j}, by decide⟩)" for i, j in reduction["pivots"]) + "]"
            if reduction["status"] != "normal-form":
                raise ValueError(f"unit-pivot attempt inconclusive (not an invalid mesh): {reduction}")
            evaluation_left = [i * 7 - 11 for i in range(len(generators))]
            evaluation_right = [i * i * 3 + i * 2 - 5 for i in range(len(generators))]
            dual_left, dual_right = (dual_values(reduction, values) for values in (evaluation_left, evaluation_right))
            weighted = weighted_period_rows(cycle_rows(reduction), evaluation_left, evaluation_right,
                                            list(range(1, len(generators) + 1)))
            weighted_data = "[" + ", ".join(f"(({entry['sample'][0]}, {entry['sample'][1]}), {entry['mass']}, {entry['charge']})"
                                             for entry in weighted) + "]"
            pairing_value = sum(paired_matrix[i][j] * evaluation_left[i] * evaluation_right[j]
                                for i in range(len(generators)) for j in range(len(generators)))
            one_sided_data = "[" + ", ".join("true" if flag else "false" for flag in one_sided) + "]"
            generator_data = "[" + ", ".join(f"({a}, {b})" for a, b in generators) + "]"
            connection += f'''
theorem meshNonloop : ∀ edge ∈ triangleEdgeOccurrences faces, edge.start ≠ edge.finish :=
  triangleEdgeOccurrences_nonloop faces (by decide)
def cutPairs := Purelib.Topology.Surface.Cut.BoundaryPairs.SewingForest.SinglePolygon.edgePairing singlePolygon meshNonloop
/-- Retain the whole computed word as closed data. Otherwise compiler
specialization can duplicate its construction inside every entry lookup. -/
def cutWord := Purelib.Topology.Surface.Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord cutPairs
def cutIntegralPairing := Purelib.Topology.Surface.Cut.IntegralPairing.CutBoundaryWord.build cutWord
def expectedGenerators : List (Nat × Nat) := {generator_data}
def expectedWord : List Int := {signed_word}
def expectedChords : List (Nat × Nat × Nat × List Int) := {chord_data}
def expectedWordTotal : List Int := {word_total}
def expectedWordMatrix : List (List Int) := {word_matrix}
def expectedOneSided : List Bool := {one_sided_data}
def expectedPairedMatrix : List (List Int) := {paired_matrix}
def expectedRemainingMatrix : List (List Int) := {remaining_matrix}
def reductionPivots : List (Purelib.LinearAlgebra.Alternating.Handle.Basic.PivotIndices cutWord.alphabet.count) := {pivot_data}
def checkedNormalForm := Purelib.LinearAlgebra.Alternating.NormalForm.Check.checkNormalForm cutIntegralPairing.paired reductionPivots
def cutAutomaticNormalForm := Purelib.Topology.Surface.Word.PairedWord.CutBoundaryWord.IntegralPairing.wordNormalForm cutIntegralPairing
def cutNormalForm : Purelib.LinearAlgebra.Alternating.NormalForm cutIntegralPairing.paired cutAutomaticNormalForm.pivots :=
  cutAutomaticNormalForm.normal
def expectedReducedMatrix : List (List Int) := {reduction['matrix']}
def expectedDualLeft : List Int := {dual_left}
def expectedDualRight : List Int := {dual_right}
def expectedPairingValue : Int := {pairing_value}
def expectedCycleRows : List (List Int) := {cycle_rows(reduction)}
def expectedWeightedRows : List ((Int × Int) × Int × Int) := {weighted_data}
def pairedLetters := Purelib.Topology.Surface.Word.PairedWord.CutBoundaryWord.pairedLetters cutWord
{lean_surgeries(len(generators), surgeries)}

example (values : Purelib.Data.Vector Int cutWord.alphabet.count) :
    cutNormalForm.reduction.backward (cutNormalForm.reduction.forward values) = values :=
  cutNormalForm.reduction.backward_forward values

example (row column : Fin cutWord.alphabet.count) (unused : row ∉ Purelib.LinearAlgebra.Alternating.Handle.Basic.handleIndices cutAutomaticNormalForm.pivots) :
    cutNormalForm.reduction.output row column = 0 := cutNormalForm.unused_row row column unused

example (index : Fin cutWord.alphabet.count) (member : index ∈ Purelib.LinearAlgebra.Alternating.Handle.Basic.handleIndices cutAutomaticNormalForm.pivots) :
    cutWord.alphabet.oneSided index = false := Purelib.Topology.Surface.Word.PairedWord.CutBoundaryWord.IntegralPairing.normalForm_paired cutIntegralPairing cutAutomaticNormalForm index member

example (index : Fin cutWord.alphabet.count) :
    cutWord.signature.total index = if cutWord.alphabet.oneSided index then 1 else 0 := Purelib.Topology.Surface.Cut.IntegralPairing.CutBoundaryWord.total_eq_oneSided cutWord index

example (row column : Fin cutWord.alphabet.count) :
    cutIntegralPairing.paired row column = -cutIntegralPairing.paired column row := cutIntegralPairing.paired_skew row column

/-- Only the generated polygon must reproduce its generated cyclic word.
The automatic forest may choose a different tree and hence a different word. -/
def checkGeneratedWord (profile : Bool) : IO Unit := do
  let started ← IO.monoMsNow
  profileLog profile "word: extracting cyclic alphabet and signature"
  let word := cutWord
  profileLog profile s!"word: {{word.letters.length}} letters in {{((← IO.monoMsNow) - started)}} ms"
  let indices := List.finRange word.alphabet.count
  let generators := indices.map fun index =>
    let edge := Purelib.Topology.Surface.Sewing.VertexSewing.OrientedEdge.map singlePolygon.patch.cut.vertexLabels (word.alphabet.generators index)
    (edge.start.val, edge.finish.val)
  let letters := word.letters.map fun letter =>
    if letter.reversed then -(Int.ofNat (letter.index.val + 1)) else Int.ofNat (letter.index.val + 1)
  let total := indices.map fun index => word.signature.total index
  let matrix := indices.map fun row => indices.map fun column => word.signature.matrix row column
  let mut chords := []
  for index in indices do
    if paired : word.alphabet.oneSided index = false then
      let chord := Purelib.Topology.Surface.Cut.Chord.CutBoundaryWord.build word index paired
      let interval := chord.interval.map fun entry =>
        if entry.letter.reversed then -(Int.ofNat (entry.letter.index.val + 1)) else Int.ofNat (entry.letter.index.val + 1)
      chords := chords ++ [(index.val, chord.first.before.length, chord.last.before.length, interval)]
  unless chords == expectedChords do
    throw (IO.userError "actual chord selection disagrees with generated occurrence positions")
  let cycleRows := cutNormalForm.reduction.cycleRows
  unless indices.map (fun row => indices.map fun column => cycleRows row column) == expectedCycleRows do
    throw (IO.userError "inverse-dual cycle rows differ from the Python chronological shears")
  let generatorsMatch := generators == expectedGenerators
  profileLog profile s!"word: generators match {{generatorsMatch}} in {{((← IO.monoMsNow) - started)}} ms"
  let lettersMatch := letters == expectedWord
  profileLog profile s!"word: letters match {{lettersMatch}} in {{((← IO.monoMsNow) - started)}} ms"
  let totalMatch := total == expectedWordTotal
  profileLog profile s!"word: totals match {{totalMatch}} in {{((← IO.monoMsNow) - started)}} ms"
  let matrixMatch := matrix == expectedWordMatrix
  profileLog profile s!"word: matrix matches {{matrixMatch}} in {{((← IO.monoMsNow) - started)}} ms"
  unless generatorsMatch && lettersMatch && totalMatch && matrixMatch do
    throw (IO.userError "the actual cyclic boundary signature differs from independently generated data")
  let oneSided := indices.map fun index => word.alphabet.oneSided index
  let paired := indices.map fun row => indices.map fun column => cutIntegralPairing.paired row column
  let remaining := indices.map fun row => indices.map fun column => cutIntegralPairing.remaining row column
  unless oneSided == expectedOneSided && paired == expectedPairedMatrix && remaining == expectedRemainingMatrix do
    throw (IO.userError "integer halving or the retained physical-boundary matrix differs from generated data")
  let reduced := indices.map fun row => indices.map fun column => cutNormalForm.reduction.output row column
  unless decide (cutAutomaticNormalForm.pivots = reductionPivots) do
    throw (IO.userError "the actual cut boundary's automatic normal form differs from the generated pivot plan")
  let pairedCanonical := Purelib.Topology.Surface.Word.Pairing.Signature.build (pairedLetters.map Purelib.Topology.Surface.Word.SignedWord.SignedGenerator.coefficients)
  unless indices.all (fun row => indices.all fun column =>
      pairedCanonical.matrix row column == 2 * cutIntegralPairing.paired row column) do
    throw (IO.userError "filtering physical-boundary occurrences changed the paired matrix")
  match checkedNormalForm with
  | .ok _ => pure ()
  | .error _ => throw (IO.userError "the executable verifier rejected a kernel-certified normal form")
  unless reduced == expectedReducedMatrix do
    throw (IO.userError "the exact unit-pivot normal form differs from generated data")
  let values := Purelib.Data.Vector.Basic.vectorOfFn fun index : Fin word.alphabet.count => (index.val : Int) * 7 - 11
  let restored := cutNormalForm.reduction.backward (cutNormalForm.reduction.forward values)
  unless indices.all (fun index => restored index == values index) do
    throw (IO.userError "the integral change of basis failed its explicit inverse")
  let other := Purelib.Data.Vector.Basic.vectorOfFn fun index : Fin word.alphabet.count =>
    (index.val : Int) * index.val * 3 + index.val * 2 - 5
  let sampleValues := Purelib.Data.Vector.Basic.vectorOfFn fun index =>
    (⟨Purelib.Data.Rat.Fraction.Cast.fromInt (values index), Purelib.Data.Rat.Fraction.Cast.fromInt (other index)⟩ : Gaussian)
  let sources := Purelib.Data.Vector.Basic.vectorOfFn fun index =>
    Purelib.Approximation.Gaussian.Geometric.GeometricApproximation.exact (sampleValues index)
  let errors := fun index : Fin word.alphabet.count => Purelib.Data.Rat.Fraction.Cast.fromInt (Int.ofNat (index.val + 1))
  for row in indices do
    let coefficients := Purelib.Riemann.Periods.WeightedPeriods.Coefficients.build (cycleRows row)
    let expected := expectedWeightedRows[row.val]!
    let sample : Gaussian := ⟨Purelib.Data.Rat.Fraction.Cast.fromInt expected.1.1, Purelib.Data.Rat.Fraction.Cast.fromInt expected.1.2⟩
    let combined := coefficients.approximation sources
    unless coefficients.combine sampleValues == sample &&
        coefficients.mass == Purelib.Data.Rat.Fraction.Cast.fromInt expected.2.1 &&
        coefficients.charge errors == Purelib.Data.Rat.Fraction.Cast.fromInt expected.2.2 do
      throw (IO.userError "weighted cycle sample or coefficient-squared error charge differs from Python data")
    for stage in [0, 1, 3] do
      unless combined.sample stage == sample && coefficients.negate.combine sampleValues == -sample &&
          coefficients.negate.mass == coefficients.mass do
        throw (IO.userError "weighted stream synchronization or negative handle orientation failed")
  let dualLeft := cutNormalForm.reduction.dualForward values
  let dualRight := cutNormalForm.reduction.dualForward other
  unless indices.map (fun index => dualLeft index) == expectedDualLeft &&
      indices.map (fun index => dualRight index) == expectedDualRight &&
      Purelib.LinearAlgebra.Alternating.Handle.Pairing.handlePairing cutAutomaticNormalForm.pivots dualLeft dualRight == expectedPairingValue do
    throw (IO.userError "dual handle evaluation differs from independent Python values")
{lean_surgery_checks(surgeries)}\
  profileLog profile s!"word: all comparisons complete in {{((← IO.monoMsNow) - started)}} ms"

example (edge : OrientedEdge vertexCount) :
    edge ∈ cutPairs.boundary.map (Purelib.Topology.Surface.Sewing.VertexSewing.OrientedEdge.map singlePolygon.patch.cut.vertexLabels) ↔
      edge ∈ triangleEdgeOccurrences faces ∧ edge.reverse ∉ triangleEdgeOccurrences faces :=
  Purelib.Topology.Surface.Cut.BoundaryPairs.SewingForest.SinglePolygon.boundary_iff singlePolygon (by decide) cutPairs edge

def checkCutPairing {{forest : SewingForest faces}} (polygon : SinglePolygon forest) (profile : Bool) : IO Unit := do
  let started ← IO.monoMsNow
  profileLog profile "pairing: starting cut comparison"
  let pairing := Purelib.Topology.Surface.Cut.BoundaryPairs.SewingForest.SinglePolygon.edgePairing polygon meshNonloop
  unless pairing.pairs.length == {cut_pairs} && pairing.boundary.length == {exterior_count} do
    throw (IO.userError "projected cut pairing disagrees with generated occurrence counts")
  let original := triangleEdgeOccurrences faces
  let expected := original.filter fun edge => decide (edge.reverse ∉ original)
  let actual := pairing.boundary.map (Purelib.Topology.Surface.Sewing.VertexSewing.OrientedEdge.map polygon.patch.cut.vertexLabels)
  unless actual.length == expected.length && actual.all (fun edge => decide (edge ∈ expected)) do
    throw (IO.userError "residual cut edges differ from the independently scanned one-sided mesh boundary")
  let word := Purelib.Topology.Surface.Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord pairing
  let cycleRoutes := Purelib.Topology.Surface.Sewing.ChordCycleBank.build word polygon.patch.cut.closed
  let primitive := fun index : Fin polygon.patch.cut.count =>
    let value := Purelib.Data.Rat.Fraction.Cast.fromInt index.val
    (⟨⟨value, 0⟩, ⟨value * value, 0⟩⟩ : PrimitivePoint)
  let sample := Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing.PrimitiveSample.build pairing primitive
  unless edgeListArea primitive polygon.patch.cut.boundary == sample.boundaryArea + sample.jumpSum + sample.defectSum do
    throw (IO.userError "cut primitive jumps or compatibility defects were dropped")
  profileLog profile s!"pairing: word extracted in {{((← IO.monoMsNow) - started)}} ms"
  let wordSample := Purelib.Topology.Surface.Cut.WordArea.CutBoundaryWord.AreaSample.build word primitive (primitive polygon.patch.cut.anchor)
  let integral := Purelib.Topology.Surface.Cut.IntegralPairing.CutBoundaryWord.build word
  let cycleBank := cycleRoutes.sample integral primitive wordSample.values
  let normal := Purelib.Topology.Surface.Word.PairedWord.CutBoundaryWord.IntegralPairing.wordNormalForm integral
  let evaluated := Purelib.Topology.Surface.Boundary.NormalFormArea.build normal.normal wordSample.values
  let cycleRows := Purelib.Topology.Surface.Sewing.NormalFormCycles.build normal.normal cycleBank
  let rowProfile := Purelib.Approximation.Budget.WeightedRowBudgets.CoefficientRows.build normal.normal.reduction.cycleRows
{lean_energy_area_checks()}\
  let pairBound := sample.samples.foldl (fun bound entry => max bound
    (max (Purelib.Data.Gaussian.Norm.Basic.normSq entry.defect.left)
      (Purelib.Data.Gaussian.Norm.Basic.normSq entry.defect.right))) 0
  if nonnegative : 0 ≤ pairBound then
    if paired : ∀ pair ∈ pairing.pairs,
        (Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (((primitive pair.first.finish).sub (primitive pair.first.start)).add
          ((primitive pair.second.finish).sub (primitive pair.second.start)))) pairBound then
      have wordBound := Purelib.Topology.Surface.Cut.WordErrors.CutWordArea.errors_of_pairing nonnegative (Purelib.Topology.Surface.Cut.BoundaryWord.ProjectedEdgePairing.boundaryWord_provenance pairing) (Purelib.Topology.Surface.Cut.WordErrors.CutBoundaryWord.AreaSample.values_apply wordSample) paired
      have _totalBound := Purelib.Topology.Surface.Cut.WordErrors.CutBoundaryWord.AreaSample.errorTotal_bounded wordSample wordBound
      let wordCount := Purelib.Approximation.Rational.Budget.Aggregate.countCoordinate polygon.patch.cut.boundary.length
      let totalBound := wordCount * (wordCount * pairBound)
      let magnitude := polygon.patch.cut.boundary.foldl (fun bound edge => max bound
        (max (max (Purelib.Data.Gaussian.Norm.Basic.normSq (primitive edge.start).left)
          (Purelib.Data.Gaussian.Norm.Basic.normSq (primitive edge.start).right))
          (max (Purelib.Data.Gaussian.Norm.Basic.normSq (primitive edge.finish).left)
            (Purelib.Data.Gaussian.Norm.Basic.normSq (primitive edge.finish).right)))) 0
      let weight := Purelib.Topology.Surface.Cut.WordAreaBounds.CutWordArea.areaWeight magnitude polygon.patch.cut.boundary.length
      unless decide (Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded wordSample.errorTotal totalBound) do
        throw (IO.userError "word error sum exceeded its complete count-dependent budget")
      for member : step in wordSample.steps do
        have _driftBound := Purelib.Topology.Surface.Cut.WordAreaBounds.CutBoundaryWord.AreaSample.step_drift_bounded wordSample polygon.patch.cut.closed nonnegative wordBound step member
        unless decide (Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded step.error pairBound ∧ Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded step.drift totalBound) do
          throw (IO.userError "a word step or accumulated prefix drift exceeded the paired-error bound")
        unless decide (Purelib.Data.Gaussian.Norm.Basic.normSq step.correction ≤ weight * pairBound) do
          throw (IO.userError "a weighted word correction exceeded the combined drift and local-error bound")
        let representative := word.alphabet.generators step.entry.letter.index
        if step.entry.letter.reversed then
          unless pairing.pairs.any (fun pair => decide (representative = pair.first ∧ step.entry.edge = pair.second)) do
            throw (IO.userError "a reversed word letter lost its exact original pair")
        else
          unless decide (step.entry.edge = representative) && step.error.left == 0 && step.error.right == 0 do
            throw (IO.userError "a forward word letter is not its literal retained generator")
      for index in List.finRange word.alphabet.count do
        have _chordBound := Purelib.Topology.Surface.Cut.ChordErrors.ChordCycleBank.Sample.errors_bounded cycleBank nonnegative wordBound index
        unless decide ((Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (cycleBank.errors index)) totalBound) do
          throw (IO.userError "a cached chord error exceeded the uniform whole-word budget")
        have _rowBound := Purelib.Topology.Surface.Boundary.NormalFormErrorBounds.errors_bounded cycleRows rowProfile (Purelib.Topology.Surface.Cut.ChordErrors.ChordCycleBank.Sample.errors_bounded cycleBank nonnegative wordBound) index
        unless decide ((Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (cycleRows.errors index)) ((rowProfile.coefficients.get index).mass * totalBound)) do
          throw (IO.userError "normal-form row error exceeded its cached squared-coefficient charge")
      let rowTarget := (rowProfile.total + 1) * (totalBound + 1)
      if rowPositive : 0 < rowTarget then
        if errors : ∀ index, (Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (cycleBank.errors index)) (rowProfile.perComponent rowTarget) then
          for index in List.finRange word.alphabet.count do
            have _rowAccurate := Purelib.Topology.Surface.Boundary.NormalFormErrorBounds.errors_accurate cycleRows rowProfile rowPositive errors index
            unless decide (Purelib.Data.Gaussian.Norm.Basic.normSq (cycleRows.errors index).left < rowTarget ∧
                Purelib.Data.Gaussian.Norm.Basic.normSq (cycleRows.errors index).right < rowTarget) do
              throw (IO.userError "the joint row allocation did not pay a transformed chord error")
          for member : pair in normal.pivots do
            have _firstAccurate := Purelib.Topology.Surface.Boundary.NormalFormErrorBounds.first_accurate cycleRows evaluated rowProfile rowPositive errors pair member
            have _lastAccurate := Purelib.Topology.Surface.Boundary.NormalFormErrorBounds.last_accurate cycleRows evaluated rowProfile rowPositive errors pair member
            let firstError := ((cycleRows.handleFirst pair).increment primitive).sub
              ((evaluated.points pair.1).sub (cycleRows.physical pair.2))
            let lastError := ((cycleRows.handleLast pair).increment primitive).sub
              ((evaluated.points pair.2).add (cycleRows.physical pair.1))
            unless decide (Purelib.Data.Gaussian.Norm.Basic.normSq firstError.left < rowTarget ∧
                Purelib.Data.Gaussian.Norm.Basic.normSq firstError.right < rowTarget ∧
                Purelib.Data.Gaussian.Norm.Basic.normSq lastError.left < rowTarget ∧
                Purelib.Data.Gaussian.Norm.Basic.normSq lastError.right < rowTarget) do
              throw (IO.userError "a retained handle orientation lost its paid row error or physical correction")
        else throw (IO.userError "the joint row budget did not cover the actual chord error bank")
      else throw (IO.userError "the transformed-row regression target must be positive")
      profileLog profile "pairing: all transformed row errors and both handle orientations checked"
      let sampledRows := Purelib.Data.Vector.Basic.vectorOfFn fun index =>
        (cycleRows.jumps index).right + (⟨1, 1⟩ : Purelib.Data.Gaussian.Basic.Canonical)
      if sampledBound : ∀ index, Purelib.Data.Gaussian.Norm.Basic.normSq
          ((cycleRows.jumps index).right - sampledRows index) ≤ 2 then
        for member : pair in normal.pivots do
          have totalBound_eq : totalBound =
              (polygon.patch.cut.boundary.length : AreaCoordinate) *
                ((polygon.patch.cut.boundary.length : AreaCoordinate) * pairBound) :=
            congrArg (fun count : AreaCoordinate => count * (count * pairBound))
              (Purelib.Approximation.Rational.Budget.Aggregate.countCoordinate_eq _)
          have rowErrors (index : Fin word.alphabet.count) :
              Purelib.Data.Gaussian.Norm.Basic.normSq (cycleRows.errors index).right ≤
                (rowProfile.coefficients.get index).mass * totalBound := by
            rw [totalBound_eq, Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical]
            exact (Purelib.Topology.Surface.Boundary.NormalFormErrorBounds.errors_bounded cycleRows rowProfile
              (Purelib.Topology.Surface.Cut.ChordErrors.ChordCycleBank.Sample.errors_bounded cycleBank nonnegative wordBound) index).2
          have _firstSample := Purelib.Topology.Surface.Boundary.NormalFormErrorBounds.first_sample_bounded
            (jumpBound := fun _ => (2 : AreaCoordinate))
            (errorBound := fun index => (rowProfile.coefficients.get index).mass * totalBound)
            cycleRows evaluated sampledRows sampledBound rowErrors pair member
          have _lastSample := Purelib.Topology.Surface.Boundary.NormalFormErrorBounds.last_sample_bounded
            (jumpBound := fun _ => (2 : AreaCoordinate))
            (errorBound := fun index => (rowProfile.coefficients.get index).mass * totalBound)
            cycleRows evaluated sampledRows sampledBound rowErrors pair member
          let firstError := -sampledRows pair.2 - ((evaluated.points pair.1).right - (cycleRows.physical pair.2).right)
          let lastError := sampledRows pair.1 - ((evaluated.points pair.2).right + (cycleRows.physical pair.1).right)
          unless decide (Purelib.Data.Gaussian.Norm.Basic.normSq firstError ≤
                2 * (2 + (rowProfile.coefficients.get pair.2).mass * totalBound) ∧
              Purelib.Data.Gaussian.Norm.Basic.normSq lastError ≤
                2 * (2 + (rowProfile.coefficients.get pair.1).mass * totalBound)) do
            throw (IO.userError "handle transfer lost the nonzero sampling error or a physical-boundary correction")
      else throw (IO.userError "the generated row perturbation did not have its declared squared error")
      profileLog profile "pairing: both sampled handle orientations checked with nonzero complex perturbations"
      let physicalHandles := normal.pivots.filter fun pair =>
        decide ((cycleRows.physical pair.1).right ≠ 0 ∨ (cycleRows.physical pair.2).right ≠ 0)
      profileLog profile s!"pairing: {{physicalHandles.length}} handles have nonzero physical-boundary corrections"
      let areaTarget := (2 * (wordCount + 1) ^ 2) * (weight + 1) * (pairBound + 1)
      let localTarget := Purelib.Approximation.Rational.Budget.Aggregate.perTerm (Purelib.Approximation.Rational.Budget.Weighted.allowance areaTarget weight)
        polygon.patch.cut.boundary.length
      if magnitudeNonnegative : 0 ≤ magnitude then
        if areaPositive : 0 < areaTarget then
          if paid : pairBound ≤ localTarget then
            if increments : ∀ entry ∈ word.alphabet.entries,
                (Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Purelib.Topology.Surface.Word.Pairing.linear entry.letter.coefficients wordSample.values)) (4 * magnitude) then
              if endpoints : ∀ entry ∈ word.alphabet.entries, (Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (primitive entry.edge.start)) magnitude then
                have _areaBound := Purelib.Topology.Surface.Cut.WordAreaBounds.CutBoundaryWord.AreaSample.correction_accurate wordSample polygon.patch.cut.closed areaPositive magnitudeNonnegative
                  (fun entry member => Purelib.Topology.Surface.Cut.WordErrors.PrimitivePoint.Bounded.mono (wordBound entry member) paid) increments endpoints
                unless decide (Purelib.Data.Gaussian.Norm.Basic.normSq wordSample.correction < areaTarget) do
                  throw (IO.userError "the full weighted word-area sum exceeded its certified request")
              else throw (IO.userError "the actual boundary endpoint maximum failed")
            else throw (IO.userError "a signed generator escaped its actual endpoint magnitude")
          else throw (IO.userError "the exact area allocation did not cover the original paired errors")
        else throw (IO.userError "the full area regression target must be positive")
      else throw (IO.userError "the actual boundary magnitude maximum is negative")
      profileLog profile "pairing: full weighted word-area request and every correction checked"
      profileLog profile "pairing: exact word provenance, all prefix drifts and all chord errors checked"
    else throw (IO.userError "the cached paired defects did not bound their actual increment mismatches")
  else throw (IO.userError "the maximum paired squared error is negative")
  profileLog profile s!"pairing: {{wordSample.steps.length}} steps sampled in {{((← IO.monoMsNow) - started)}} ms"
  unless word.alphabet.entries.map Purelib.Topology.Surface.Cut.BoundaryWord.CutWordEntry.edge == polygon.patch.cut.boundary do
    throw (IO.userError "word extraction changed the cyclic cut boundary order")
  for index in List.finRange word.alphabet.count do
    unless Purelib.Topology.Surface.Word.SignedWord.SignedGenerator.occurrences ⟨index, false⟩ word.letters == 1 &&
        Purelib.Topology.Surface.Word.SignedWord.SignedGenerator.occurrences ⟨index, true⟩ word.letters == (if word.alphabet.oneSided index then 0 else 1) do
      throw (IO.userError "word extraction dropped or reused a signed occurrence")
    unless (cycleRoutes.coordinates index).index == index do
      throw (IO.userError "cached chord coordinates changed alphabet order")
    match cycleBank.coordinates index with
    | .boundary _ _ =>
        unless (cycleRoutes.cycles index).path.cutEdges.isEmpty do
          throw (IO.userError "one-sided boundary acquired a fictitious closed chord")
    | .paired position _ chord route jump =>
        let intervalTotal := Purelib.Topology.Surface.Word.Pairing.Signature.build (Purelib.Topology.Surface.Cut.WordArea.CutWordArea.word chord.interval)
        let actualJump := Purelib.Topology.Surface.Cut.JumpPaths.CutPath.increment primitive route.path.cutEdges
        let decomposed := (jump.rowValue.add jump.physicalValue).add jump.error
        unless jump.path.cutEdges == route.path.cutEdges &&
            (List.finRange word.alphabet.count).all (fun column => intervalTotal.total column ==
            integral.paired position column + jump.physicalCoefficients column) &&
            actualJump.left == jump.jump.left && actualJump.right == jump.jump.right &&
            jump.jump.left == decomposed.left && jump.jump.right == decomposed.right do
          throw (IO.userError "chord jump lost its paired row, physical interval, or local error correction")
        unless (List.finRange vertexCount).all (fun vertex =>
            Purelib.Topology.Chain.PathBoundary.wordBoundaryAt OrientedEdge.start OrientedEdge.finish jump.path.surfaceEdges vertex == 0) &&
            jump.path.surfaceEdges.all (fun edge => decide (edge ∈ original ∨ edge.reverse ∈ original)) do
          throw (IO.userError "chord jump is not a closed word on the actual surface mesh")
  let zeroPrimitive := fun _ : Fin polygon.patch.cut.count => Purelib.Topology.Polygon.Stokes.PrimitivePoint.zero
  let zeroSample := cycleRoutes.sample integral zeroPrimitive (Purelib.Topology.Surface.Cut.WordArea.CutBoundaryWord.generatorValues word zeroPrimitive)
  for index in List.finRange word.alphabet.count do
    let retained := ((zeroSample.coordinates index).coordinate.cycle cycleRoutes.anchor).path
    let actual := (cycleRoutes.cycles index).increment zeroPrimitive
    unless retained.cutEdges == (cycleRoutes.cycles index).path.cutEdges &&
        retained.surfaceEdges == (cycleRoutes.cycles index).path.surfaceEdges &&
        actual.left == (zeroSample.jumps index).left && actual.right == (zeroSample.jumps index).right &&
        (zeroSample.jumps index).left == 0 && (zeroSample.jumps index).right == 0 do
      throw (IO.userError "resampling changed fixed cycle paths or reused stale primitive readings")
  unless edgeListArea primitive polygon.patch.cut.boundary ==
      edgeArea (primitive polygon.patch.cut.anchor) (Purelib.Topology.Surface.Word.Pairing.linear word.signature.total wordSample.values) +
      Purelib.Topology.Surface.Word.Pairing.contract (fun row column => word.signature.matrix row column) wordSample.values + wordSample.correction do
    throw (IO.userError "the computed word matrix lost an endpoint or compatibility correction")
  unless edgeListArea primitive polygon.patch.cut.boundary ==
      Purelib.Topology.Surface.Word.Pairing.contract (fun row column => word.signature.matrix row column) wordSample.values + wordSample.closedCorrection do
    throw (IO.userError "closedness discarded rather than paid the accumulated endpoint error")
  unless edgeListArea primitive polygon.patch.cut.boundary ==
      2 * Purelib.Topology.Surface.Word.Pairing.contract (fun row column => integral.paired row column) wordSample.values +
        Purelib.Topology.Surface.Word.Pairing.contract (fun row column => integral.remaining row column) wordSample.values + wordSample.closedCorrection do
    throw (IO.userError "integer pairing discarded mixed or one-sided boundary contributions")
  for row in List.finRange word.alphabet.count do
    let actual := (cycleRows.chains row).increment primitive
    unless actual.left == (cycleRows.jumps row).left && actual.right == (cycleRows.jumps row).right &&
        (List.finRange vertexCount).all (fun vertex => (cycleRows.chains row).boundary vertex == 0) do
      throw (IO.userError "transformed cycle chain lost its actual increment or closed boundary")
  for pair in normal.pivots do
    let first := (cycleRows.handleFirst pair).increment primitive
    let last := (cycleRows.handleLast pair).increment primitive
    let expectedFirst := (evaluated.points pair.1).sub ((cycleRows.physical pair.2).add (cycleRows.errors pair.2))
    let expectedLast := ((evaluated.points pair.2).add (cycleRows.physical pair.1)).add (cycleRows.errors pair.1)
    unless first.left == expectedFirst.left && first.right == expectedFirst.right &&
        last.left == expectedLast.left && last.right == expectedLast.right do
      throw (IO.userError "actual handle-chain increments disagree with dual coordinates and retained corrections")
  unless edgeListArea primitive polygon.patch.cut.boundary == 2 * evaluated.area +
      Purelib.Topology.Surface.Word.Pairing.contract (fun row column => integral.remaining row column) wordSample.values + wordSample.closedCorrection &&
      evaluated.area == handleArea normal.pivots evaluated.points do
    throw (IO.userError "computed handle areas lost the physical-boundary or compatibility correction")
  profileLog profile s!"pairing: matrix contractions checked in {{((← IO.monoMsNow) - started)}} ms"
  let jumpPaths := Purelib.Topology.Surface.Cut.JumpBank.ProjectedEdgePairing.jumpPaths pairing polygon.patch.cut.closed
  unless jumpPaths.entries.length == pairing.pairs.length do
    throw (IO.userError "the jump-path bank does not cover all retained pairs")
  for entry in jumpPaths.entries do
    let pairSample := Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair.Sample.build primitive entry.pair
    let firstIncrement := Purelib.Topology.Surface.Cut.JumpPaths.CutPath.increment primitive entry.paths.start.cutEdges
    let lastIncrement := Purelib.Topology.Surface.Cut.JumpPaths.CutPath.increment primitive entry.paths.finish.cutEdges
    unless firstIncrement.left == pairSample.startJump.left && firstIncrement.right == pairSample.startJump.right &&
        lastIncrement.left == pairSample.finishJump.left && lastIncrement.right == pairSample.finishJump.right do
      throw (IO.userError "the retained cut words lost their primitive increments")
    for (word, anchor) in [(entry.paths.start.surfaceEdges, polygon.patch.cut.vertexLabels entry.pair.first.start),
        (entry.paths.finish.surfaceEdges, polygon.patch.cut.vertexLabels entry.pair.first.finish)] do
      let arrived := word.foldl (fun (state : Bool × Fin vertexCount) edge =>
        (state.1 && decide (edge.start = state.2), edge.finish)) (true, anchor)
      unless arrived.1 && decide (arrived.2 = anchor) do
        throw (IO.userError "a projected jump word is not closed at its actual lifted endpoint")
      unless word.all (fun edge => decide (edge ∈ original ∨ edge.reverse ∈ original)) do
        throw (IO.userError "a jump word left the original lifted mesh")
'''
            connection_check += '''  checkGeneratedWord (args.contains "--profile")
  checkCutPairing singlePolygon (args.contains "--profile")
  checkCutPairing connectedAutomatic (args.contains "--profile")
'''
    return format_lean(f'''module

import Purelib.Approximation.Gaussian.Geometric
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Energy.Polygon
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Pairing
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Check
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Chain.PathBoundary
import Purelib.Topology.Mesh.DualWalks
import Purelib.Topology.Mesh.EdgeCancellation
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.DualCoordinateBounds
import Purelib.Topology.Surface.Boundary.HandleAreaBudgets
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Chord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Cut.WordErrors
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.NormalFormMagnitude
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.Selection
import Purelib.Topology.Surface.Word.SignedWord
import Purelib.Topology.Surface.Word.Surgery
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Budget.WeightedRowBudgets
import Purelib.Data.Rat.Fraction.Order
import Purelib.Topology.Surface.Cut.BoundaryPairs
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Cut.ChordErrors
import Purelib.Topology.Surface.Cut.WordAreaBounds
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Topology.Surface.Boundary.NormalFormArea
import Purelib.Topology.Surface.Cut.JumpBank
import Purelib.Topology.Surface.Sewing.NormalFormCycles
import Purelib.Topology.Surface.Boundary.NormalFormErrorBounds
import Purelib.Riemann.Periods.CorrectedPeriodArea
import Purelib.Topology.Surface.Cut.GeneratorBounds
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Mesh.Replay.DualReplay

/-!
Generated by scripts/generators/sewing.py; do not edit witness data.
Reproduce with --input and --output; --check rejects stale generated output.
This is a finite sewing regression, not a root or period certificate.
-/

open Purelib.Topology.Surface.Cut.BoundaryPairs
open Purelib.Topology.Surface.Cut.WordArea
open Purelib.Topology.Surface.Cut.ChordErrors
open Purelib.Topology.Surface.Cut.WordAreaBounds
open Purelib.Topology.Surface.Word.PairedWord
open Purelib.Topology.Surface.Boundary.NormalFormArea
open Purelib.Topology.Surface.Cut.JumpBank
open Purelib.Topology.Surface.Sewing.NormalFormCycles
open Purelib.Topology.Surface.Boundary.NormalFormErrorBounds
open Purelib.Riemann.Periods.CorrectedPeriodArea
open Purelib.Topology.Surface.Cut.GeneratorBounds
open Purelib.Riemann.Periods.WeightedPeriods
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
open Purelib.Topology.Mesh.Replay.DualReplay
open Purelib.Topology.Polygon.Stokes (PrimitivePoint OrientedTriangle OrientedEdge triangleEdgeOccurrences edgeListArea triangleWedgeSum edgeArea)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch SewingTree)
open Purelib.Topology.Mesh.EdgeCancellation (cancelEdges)
open Purelib.Riemann.Readings.PrimitiveAreaBounds (AreaCoordinate)
open Purelib.Topology.Surface.Sewing.SewingForest (SewingForest)
open Purelib.Topology.Surface.Sewing.SewingConnected.SewingForest (SinglePolygon)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Mesh.DualWalks (DualConnection)
open Purelib.Topology.Surface.Word.Surgery (InterlacedWord)
open Purelib.Topology.Surface.Word.Selection (selectWord)
open Purelib.Topology.Surface.Word.NormalForm (normalizeWord)

private instance (point : PrimitivePoint) (bound : AreaCoordinate) : Decidable (Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded point bound) :=
  inferInstanceAs (Decidable (Purelib.Data.Gaussian.Basic.Canonical.normSq point.left ≤ bound ∧
    Purelib.Data.Gaussian.Basic.Canonical.normSq point.right ≤ bound))

def profileLog (enabled : Bool) (message : String) : IO Unit := do
  if enabled then
    let output ← IO.getStdout
    output.putStr message
    output.putStr "\\n"
    output.flush

def vertexCount : Nat := {count}
def faceCount : Nat := {len(faces)}
def faceData : Purelib.Data.Vector (OrientedTriangle vertexCount) faceCount :=
  {data}
def faces : Fin faceCount → OrientedTriangle vertexCount := faceData
def trees : List (SewingTree faceCount) := [
  {trees}]
def localPrimitiveData : Purelib.Data.Vector (PrimitiveValues 3) faceCount :=
  {primitive_data}
def expectedPrimitiveValues : List (List Int) := {primitive_values}
def expectedPrimitiveCharges : List (List Int) := {primitive_charges}
def expectedPrimitiveFaces : List (List (List Int)) := {primitive_faces}
def expectedPrimitiveTotals : List (List Int) := {primitive_totals}
def expectedPrimitiveBoundaries : List (List (List Int)) := {primitive_boundaries}
def expectedPrimitiveContacts : List (List (List Int)) := {primitive_contacts}

def certified : SewingForest faces := (Purelib.Topology.Surface.Sewing.SewingForest.checkTrees faces trees).toOption.get (by decide)
def rightNestedTrees : List (SewingTree faceCount) := [
  {right_trees}]
def rightNestedCertified : SewingForest faces := (Purelib.Topology.Surface.Sewing.SewingForest.checkTrees faces rightNestedTrees).toOption.get (by decide)
{connection}

example : certified.patches.length = {len(patches)} := by decide
example : (certified.patches.flatMap Purelib.Topology.Surface.Sewing.SewingTree.SewnPatch.boundary).length = {boundary_count} := by decide
example : (cancelEdges (certified.patches.flatMap Purelib.Topology.Surface.Sewing.SewingTree.SewnPatch.boundary)).internalEdges.length = {cut_pairs} := by decide
example : (cancelEdges (certified.patches.flatMap Purelib.Topology.Surface.Sewing.SewingTree.SewnPatch.boundary)).boundary.length = {exterior_count} := by decide

example (primitive : Fin vertexCount → PrimitivePoint) :
    edgeListArea primitive (certified.patches.flatMap Purelib.Topology.Surface.Sewing.SewingTree.SewnPatch.boundary) = triangleWedgeSum primitive faces :=
  certified.boundary_area primitive

public def main (args : List String) : IO Unit := do
  profileLog (args.contains "--profile") "sewing regression profiling enabled"
  let automatic := Purelib.Topology.Surface.Sewing.SewingForest.build faces
{connection_check}\
  unless automatic.patches.length == {len(patches)} &&
      (automatic.patches.flatMap Purelib.Topology.Surface.Sewing.SewingTree.SewnPatch.boundary).length == {boundary_count} do
    throw (IO.userError "automatic sewing disagrees with the independently generated forest counts")
  unless (certified.patches.flatMap Purelib.Topology.Surface.Sewing.SewingTree.SewnPatch.faceIndices).length == faceCount do
    throw (IO.userError "face occurrences were dropped or repeated")
  let primitivePatches := certified.patches ++ rightNestedCertified.patches
  let contactRows := primitivePatches.map fun patch =>
    let contacts := Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts.ContactBank.build patch.assembly
    contacts.entries.map fun contact =>
      [Purelib.Data.Rat.Fraction.Cast.fromInt contact.left.source.val,
        Purelib.Data.Rat.Fraction.Cast.fromInt contact.left.first.val, Purelib.Data.Rat.Fraction.Cast.fromInt contact.left.last.val,
        Purelib.Data.Rat.Fraction.Cast.fromInt contact.right.source.val,
        Purelib.Data.Rat.Fraction.Cast.fromInt contact.right.first.val, Purelib.Data.Rat.Fraction.Cast.fromInt contact.right.last.val,
        contact.mismatch localPrimitiveData]
  unless contactRows == expectedPrimitiveContacts.map (List.map (List.map Purelib.Data.Rat.Fraction.Cast.fromInt)) do
    throw (IO.userError "geometry-only source contacts differ from the independent Python seam replay")
  unless expectedPrimitiveValues.length == primitivePatches.length && expectedPrimitiveCharges.length == primitivePatches.length &&
      expectedPrimitiveFaces.length == primitivePatches.length && expectedPrimitiveTotals.length == primitivePatches.length &&
      expectedPrimitiveBoundaries.length == primitivePatches.length do
    throw (IO.userError "generated primitive sample bank has incomplete patch coverage")
  for (patch, (expectedValues, (expectedCharges, (expectedFaces, (expectedTotals, expectedBoundary))))) in
      primitivePatches.zip (expectedPrimitiveValues.zip (expectedPrimitiveCharges.zip
        (expectedPrimitiveFaces.zip (expectedPrimitiveTotals.zip expectedPrimitiveBoundaries)))) do
    let request := Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests.Request.build patch.assembly 1 (by decide)
    let sample := Purelib.Topology.Surface.Sewing.PrimitiveSewing.SewnPatch.primitiveSample patch localPrimitiveData
    unless (List.finRange patch.cut.count).map (fun index => (sample.values index).re) ==
        expectedValues.map Purelib.Data.Rat.Fraction.Cast.fromInt &&
        (List.finRange patch.cut.count).all (fun index => (sample.values index).im == 0) &&
        sample.charges == expectedCharges.map Purelib.Data.Rat.Fraction.Cast.fromInt &&
        sample.charges.length + 1 == patch.faceIndices.length do
      throw (IO.userError "actual sewn primitive values or retained seam charges differ from independent Python replay")
    let bank := Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceBank.build sample.readings
    let rows := bank.entries.map fun trace =>
      [Purelib.Data.Rat.Fraction.Cast.fromInt trace.source.val, Purelib.Data.Rat.Fraction.Cast.fromInt trace.triangle.first.val,
       Purelib.Data.Rat.Fraction.Cast.fromInt trace.triangle.second.val, Purelib.Data.Rat.Fraction.Cast.fromInt trace.triangle.third.val,
       (trace.errors 0).re, (trace.errors 1).re, (trace.errors 2).re,
       Purelib.Data.Rat.Fraction.Cast.fromInt trace.depth, trace.charge, trace.allowance]
    unless rows == expectedFaces.map (List.map Purelib.Data.Rat.Fraction.Cast.fromInt) &&
        bank.entries.all (fun trace => (List.finRange 3).all (fun index => (trace.errors index).im == 0)) &&
        [bank.totalAllowance, bank.squaredErrors, Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting.totalCharge sample.readings,
          Purelib.Data.Rat.Fraction.Cast.fromInt request.profile.depth, Purelib.Data.Rat.Fraction.Cast.fromInt request.profile.factor,
          Purelib.Data.Rat.Fraction.Cast.fromInt request.profile.faces, request.amplification] == expectedTotals.map Purelib.Data.Rat.Fraction.Cast.fromInt &&
        0 < request.tolerance && request.amplification * request.tolerance < 1 &&
        bank.squaredErrors ≤ 2 * bank.totalAllowance do
      throw (IO.userError "actual face increments or whole-mesh seam allowances differ from independent Python replay")
    unless expectedBoundary.length == patch.cut.boundary.length do
      throw (IO.userError "generated primitive boundary owners have incomplete coverage")
    let zeroData := fun _ : Fin faceCount => Purelib.Data.Vector.Basic.vectorOfFn (fun _ : Fin 3 => (0 : Purelib.Data.Gaussian.Basic.Canonical))
    let zeroBank := Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.FaceBank.build (Purelib.Topology.Surface.Sewing.PrimitiveSewing.SewnPatch.primitiveSample patch zeroData).readings
    for position in List.finRange patch.cut.boundary.length do
      let edge := patch.cut.boundary[position.val]'position.isLt
      let owner := Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary.boundaryOwner patch.cut edge (List.getElem_mem position.isLt)
      let reading := Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary.FaceBank.EdgeReading.build bank owner
      let row := [Purelib.Data.Rat.Fraction.Cast.fromInt edge.start.val, Purelib.Data.Rat.Fraction.Cast.fromInt edge.finish.val,
        Purelib.Data.Rat.Fraction.Cast.fromInt owner.position.val, Purelib.Data.Rat.Fraction.Cast.fromInt reading.trace.source.val,
        Purelib.Data.Rat.Fraction.Cast.fromInt owner.first.val, Purelib.Data.Rat.Fraction.Cast.fromInt owner.last.val,
        reading.localIncrement.re, reading.error.re, reading.allowance]
      unless row == (expectedBoundary[position.val]?.getD []).map Purelib.Data.Rat.Fraction.Cast.fromInt &&
          reading.localIncrement.im == 0 && reading.error.im == 0 &&
          Purelib.Data.Gaussian.Norm.Basic.normSq reading.error ≤ reading.allowance do
        throw (IO.userError "boundary owner selected the wrong cut occurrence or dropped inherited primitive errors")
      let zeroReading := Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary.FaceBank.EdgeReading.build zeroBank owner
      unless zeroReading.trace.source == reading.trace.source && zeroReading.localIncrement == 0 &&
          zeroReading.error == 0 && zeroReading.allowance == 0 do
        throw (IO.userError "reusing a geometric boundary owner retained stale primitive values or errors")
  let cancellation := cancelEdges (automatic.patches.flatMap Purelib.Topology.Surface.Sewing.SewingTree.SewnPatch.boundary)
  unless cancellation.internalEdges.length == {cut_pairs} && cancellation.boundary.length == {exterior_count} do
    throw (IO.userError "cut pairs or the original exterior boundary were lost")
  for patch in automatic.patches do
    unless patch.boundary.length == patch.faceIndices.length + 2 && patch.seams.length + 1 == patch.faceIndices.length do
      throw (IO.userError "tree-sewing count invariant failed")
    let cut := patch.cut
    unless (cut.boundary.map fun edge => edge.start.val).eraseDups.length == patch.boundary.length &&
        cut.triangles.length == patch.faceIndices.length do
      throw (IO.userError "cut occurrences were identified or cut triangles were lost")
    let cutPrimitive := fun index : Fin cut.count =>
      let value := Purelib.Data.Rat.Fraction.Cast.fromInt index.val
      (⟨⟨value, 0⟩, ⟨value * value, 0⟩⟩ : PrimitivePoint)
    unless edgeListArea cutPrimitive cut.boundary == edgeListArea cutPrimitive (cut.triangles.flatMap Purelib.Topology.Polygon.Stokes.OrientedTriangle.boundary) do
      throw (IO.userError "independent cut-vertex primitives failed exact Stokes")
  let primitive := fun index : Fin vertexCount =>
    let value := Purelib.Data.Rat.Fraction.Cast.fromInt index.val
    (⟨⟨value, value * value⟩, ⟨value * value * value, -value⟩⟩ : PrimitivePoint)
  unless edgeListArea primitive (automatic.patches.flatMap Purelib.Topology.Surface.Sewing.SewingTree.SewnPatch.boundary) == triangleWedgeSum primitive faces do
    throw (IO.userError "ordered sewing changed the exact Stokes area")
  if faceCount != 0 then
    unless !(Purelib.Topology.Surface.Sewing.SewingForest.checkTrees faces []).isOk && !(Purelib.Topology.Surface.Sewing.SewingForest.checkTrees faces (trees ++ trees)).isOk do
      throw (IO.userError "missing or duplicated face certificates were accepted")
  profileLog true ("sewing certificate passed: faces={len(faces)}, patches={len(patches)}, " ++
    "boundary occurrences={boundary_count}, cut pairs={cut_pairs}, exterior edges={exterior_count}; " ++
    "exact replay, coverage and area")
''')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    count, faces = read_mesh(args.input)
    output = render(count, faces, forest(faces))
    args.output = args.output.resolve()
    if args.check:
        if not args.output.exists() or args.output.read_text() != output:
            raise SystemExit(f"stale sewing certificate: {args.output}")
    else:
        args.output.write_text(output)


if __name__ == "__main__":
    main()
