# *Divine Proportions* formalization coverage

Source: N. J. Wildberger, *Divine Proportions: Rational Trigonometry to
Universal Geometry* (321-page supplied PDF).  This ledger is deliberately
source-numbered.  `pending` means that no claim of formal coverage is made.
`corrected` means that Lean exposed a missing hypothesis or false statement in
the printed source and the strongest valid nearby statement is formalized with
the discrepancy documented.

The source inventory comprises:

- 121 numbered theorems (the complete index on pp. 289–290);
- Examples 2.1–2.19, 3.1–3.8, 5.1–5.2, 6.1–6.6, 7.1–7.4,
  8.1–8.5, 10.1, 11.1, 12.1–12.2, 13.1–13.3, 14.1–14.12,
  15.1–15.9, 17.1–17.4, 18.1, 19.1–19.10, 23.1, 24.1–24.2,
  25.1, and 27.1–27.15;
- Exercises 1.1–1.2, 2.1–2.9, 3.1–3.17, 4.1–4.6, 5.1–5.19,
  6.1–6.7, 7.1–7.15, 8.1–8.20, 9.1–9.7, 10.1–10.12,
  11.1–11.11, 12.1–12.8, 13.1–13.7, 14.1–14.5, 15.1–15.18,
  16.1–16.8, 17.1–17.6, 18.1–18.3, 19.1–19.5, 20.1–20.4,
  22.1–22.4, 24.1, 25.1–25.3, 26.1–26.4, 27.1–27.3, and B.1;
- solved Problems 1–25, including the applications in Chapters 20–25;
- the unnumbered Appendix A calculations for the circle, ellipse, hyperbola,
  parabola, two cardioids, limacon/trisectrix, astroid, eight curve, bullet
  nose, deltoid, hippopede, lemniscate of Bernoulli, and folium of Descartes;
- Appendix B's defining ellipson equation, coordinate and oblique cross-section
  claims, symmetry observation, and Exercise B.1.

The chapter ranges above are the complete inventory key for examples and
“problems for the reader”.  The chapter detail below records their Lean
declarations, finite encodings, and any agreed constructive boundary.

## Numbered theorems

| No. | Book theorem | Page | Lean declaration | Status |
|---:|---|---:|---|---|
| 1 | Quadratic compatibility | 33 | `DivineProportions.quadraticCompatibility_of_distinct_centres`; `quadraticCompatibility_same_centre` | corrected |
| 2 | Line through two points | 38 | `lineThrough`; `lineThrough_unique` | formalized |
| 3 | Collinear points | 39 | `collinear_iff_pointDeterminant_eq_zero` | formalized |
| 4 | Concurrent lines | 39 | `lineDeterminant_eq_zero_of_concurrent` | formalized |
| 5 | Point on two lines | 40 | `lineIntersection`; `lineIntersection_unique` | formalized |
| 6 | Parallel to a line | 41 | `parallelThrough`; `parallelThrough_unique` | formalized |
| 7 | Altitude to a line | 41 | `altitudeThrough`; `altitudeThrough_unique` | formalized |
| 8 | Foot of an altitude | 42 | `altitudeFoot`; `altitudeFoot_unique` | formalized |
| 9 | Affine combination | 46 | `affineCombination_iff_on_line`; `affineWeights_unique` | formalized |
| 10 | Thales’ theorem | 48 | `thales_parallel` | formalized |
| 11 | Parallelogram center | 49 | `parallelogram_center` | formalized |
| 12 | Perpendicular bisector | 50 | `perpendicularBisector`; `perpendicularBisector_perpendicular` | formalized |
| 13 | Reflection of a point in a line | 52 | `reflectPoint_formula` | formalized |
| 14 | Rotation of a line in a point | 53 | `rotateLineInPoint_contains_iff` | formalized |
| 15 | Reflection of a line in a line | 54 | `reflectLine`; `reflectLine_contains_reflectPoint` | formalized |
| 16 | Reflection | 55 | `reflection_composition` | formalized |
| 17 | Lineation | 56 | `lineation_composition` | formalized |
| 18 | Cyclic reflection | 56 | `cyclic_reflection_right`; `cyclic_reflection_left` | formalized |
| 19 | Null line | 60 | `null_line_iff_quadrance_zero` | formalized |
| 20 | Midpoint | 60 | `midpoint_theorem`; `midpoint_unique_of_equal_quadrance` | formalized |
| 21 | Parallelogram quadrance | 62 | `parallelogram_quadrance` | formalized |
| 22 | Triple quad formula | 63 | `triple_quad_formula`; `archimedes_quadrance_identity` | formalized |
| 23 | Pythagoras’ theorem | 65 | `pythagoras_iff_perpendicular` | formalized |
| 24 | Equal quadrance to two points | 66 | `equal_quadrance_iff_perpendicularBisector_contains` | formalized |
| 25 | Quadrance to a line | 67 | `pointLineQuadrance_formula` | formalized |
| 26 | Quadrea | 68 | `quadrea_coordinate_formula`; `quadrea_ne_zero_iff_not_collinear` | formalized |
| 27 | Right quadrea | 68 | `right_quadrea`; `right_triangle_quadrea` | formalized |
| 28 | Triangle quadrea | 69 | `triangle_quadrea` | formalized |
| 29 | Archimedes’ formula | 70 | `archimedes_formula` | formalized |
| 30 | Two quad triples | 70 | `two_quad_triples`; `two_quad_triples_common_value` | formalized |
| 31 | Quadruple quad formula | 71 | `quadruple_quad_formula` | formalized |
| 32 | Brahmagupta’s identity | 72 | `brahmagupta_identity` | formalized |
| 33 | Spread plus cross | 76 | `spread_add_cross` | formalized |
| 34 | Spread number | 76 | `spread_isSpreadNumber`; `spreadNumber_realized` | formalized |
| 35 | Spread ratio | 77 | `spread_ratio` | formalized |
| 36 | Cross ratio | 78 | `cross_ratio` | formalized |
| 37 | Twist ratio | 78 | `twist_ratio` | formalized |
| 38 | Complementary spreads | 79 | `complementary_spreads` | formalized |
| 39 | Perpendicular spreads | 79 | `perpendicular_spreads` | formalized |
| 40 | Spread law | 80 | `spread_law` | formalized |
| 41 | Cross law | 81 | `cross_law` | formalized |
| 42 | Quadrea spread | 82 | `quadrea_spread` | formalized |
| 43 | Spread from points | 84 | `spread_from_points` | formalized |
| 44 | Cross from points | 84 | `cross_from_points` | formalized |
| 45 | Vertex bisector | 85 | `vertex_bisector` | formalized |
| 46 | Equal quadrance to two lines | 88 | `equal_pointLineQuadrance_iff_on_vertexBisector` | formalized |
| 47 | Triple spread formula | 89 | `triple_spread_formula`; `three_lines_form_spreadTriple` | formalized |
| 48 | Spread from ratio | 91 | `spread_from_ratio` | formalized |
| 49 | Triple cross formula | 92 | `triple_cross_formula` | formalized |
| 50 | Triple twist formula | 93 | `triple_twist_formula` | formalized |
| 51 | Equal spreads | 94 | `equal_spreads` | formalized |
| 52 | Spread reflection | 95 | `spread_reflection` | formalized |
| 53 | Two spread triples | 98 | `two_spread_triples` | formalized |
| 54 | Quadruple spread formula | 99 | `quadruple_spread_formula` | formalized |
| 55 | Quadruple cross formula | 100 | `quadruple_cross_formula` | formalized |
| 56 | Three equal spreads | 101 | `three_equal_spreads` | formalized |
| 57 | Recursive spreads | 102 | `recursive_spreads` | formalized |
| 58 | Consecutive spreads | 103 | `consecutive_spreads` | formalized |
| 59 | Spread polynomial formula | 106 | `spread_polynomial_formula` | formalized |
| 60 | Spread composition | 110 | `spread_polynomial_composition` | formalized |
| 61 | Triple turn formula | 115 | `triple_turn_formula` | formalized |
| 62 | Signed area | 117 | `signed_area`; `fan_signed_area_independent` | formalized |
| 63 | Bretschneider’s formula | 118 | `bretschneider_formula` | formalized |
| 64 | Null isosceles | 121 | `null_isosceles` | formalized |
| 65 | Pons Asinorum | 122 | `pons_asinorum` | formalized |
| 66 | Isosceles triangle | 122 | `isosceles_triangle` | formalized |
| 67 | Isosceles median | 123 | `isosceles_median` | formalized |
| 68 | Isosceles reflection | 124 | `isosceles_reflection` | formalized |
| 69 | Equilateral triangle | 125 | `equilateral_triangle` | formalized |
| 70 | Right midpoint | 126 | `right_midpoint` | formalized |
| 71 | Median triangle | 128 | `median_triangle`; `median_side₁₂_quadrance` | formalized |
| 72 | Triangle proportions | 131 | `triangle_proportions`; `triangle_proportions_cleared` | formalized |
| 73 | Quadrilateral proportions | 133 | `quadrilateral_proportions`; `quadrilateral_proportions_cleared` | formalized |
| 74 | Two struts | 134 | `two_struts`; `two_struts_of_proportions` | formalized |
| 75 | Stewart’s theorem | 136 | `stewart` | formalized |
| 76 | Median quadrance | 137 | `median_quadrance` | formalized |
| 77 | Median spreads | 138 | `median_spreads`; `median_spreads_cleared` | formalized |
| 78 | Menelaus’ theorem | 139 | `menelaus`; `menelaus_cleared` | formalized |
| 79 | Alternate spreads | 140 | `alternate_spreads`; `alternate_spreads_cleared` | formalized |
| 80 | Ceva’s theorem | 141 | `ceva`; `ceva_cleared` | formalized |
| 81 | Circumcenter | 143 | `circumcenterPoint`; `circumcenter` | formalized |
| 82 | Extended spread law | 144 | `extended_spread_law`; `circumquadrea_identity` | formalized |
| 83 | Circumcenter formula | 146 | `circumcenterFormula`; `circumcenter_formula` | formalized |
| 84 | Affine circumcenter | 146 | `affineCircumcenterPoint`; `affine_circumcenter` | formalized |
| 85 | Orthocenter | 147 | `orthocenterPoint`; `orthocenter` | formalized |
| 86 | Orthocenter formula | 149 | `orthocenterFormula`; `orthocenter_formula` | formalized |
| 87 | Affine orthocenter | 149 | `affineOrthocenterPoint`; `affine_orthocenter` | formalized |
| 88 | Incenter | 150 | `incenter` | formalized |
| 89 | Incenter spread | 151 | `incenter_spread`; `normalized_incenter_third_spread_eq_cross` | formalized |
| 90 | Inquadrance | 153 | `inquadrance`; `inquadrance_cleared` | formalized |
| 91 | Isometries preserve collinearity | 157 | `PlaneIsometry.preservesCollinearity`; `PlaneIsometry.preservesQuadrea` | formalized |
| 92 | Specifying isometries | 157 | `PlaneIsometry.specifiedByReferencePoints`; `PlaneIsometry.fixingReferencePoints_eq_identity` | formalized |
| 93 | Orthogonality | 157 | `PlaneIsometry.orthogonalityClassification`; `perpendicularUnitPair_orientations` | formalized |
| 94 | Classification of isometries | 158 | `PlaneIsometry.isometryClassification`; `PlaneIsometry.translation_orthogonality_unique` | formalized |
| 95 | Order three star | 160 | `order_three_star`; `orderThreeStar`; `RegularThreeStar` | formalized |
| 96 | Order five star | 161 | `order_five_star`; `orderFiveStar`; `RegularFiveStar` | formalized |
| 97 | Order seven star | 162 | `order_seven_star`; `orderSevenStar`; `RegularSevenStar` | formalized |
| 98 | Polygon triangle | 165 | `polygon_triangle`; `PolygonTriangleConfiguration`; `reflectPoint_chord_quadrance_eq_spread` | formalized |
| 99 | Conic center | 168 | `Conic.conic_center`; `Conic.centerPoint`; `Conic.isCenter_iff_rotationInvariant` | formalized |
| 100 | Circle uniqueness | 171 | `Conic.circle_uniqueness`; `Conic.circle_has_unique_presentation` | formalized |
| 101 | Parabola uniqueness | 173 | `Conic.parabola_uniqueness`; `Conic.parabola_has_unique_focus_directrix` | formalized |
| 102 | Conic line intersection | 176 | `Conic.conic_line_intersection`; `Conic.evaluate_thalesPoint` | formalized |
| 103 | Right diameter | 177 | `Conic.right_diameter`; `Conic.right_diameter_of_center_eq_midpoint` | corrected |
| 104 | Circle chord | 178 | `Conic.circle_chord`; `Conic.radius_eq_zero_of_equal_radii_and_null_separation` | formalized |
| 105 | Subtended spread | 178 | `Conic.subtended_spread`; `Conic.lineThrough_circle_points_nonNull` | formalized |
| 106 | Equal products | 179 | `Conic.equal_products`; `Conic.chord_quadrance_product_eq_circle_power` | formalized |
| 107 | Projective circle | 181 | `Conic.projective_circle`; `Conic.projectiveCirclePoint_exists`; `Conic.projectiveCirclePoint_contains` | formalized |
| 108 | Unit circle | 182 | `Conic.unit_circle`; `Conic.unitCirclePoint_exists`; `Conic.unitCirclePoint_contains` | formalized |
| 109 | Cyclic quadrilateral | 183 | `Quadrilateral.cyclic_quadrilateral`; `Quadrilateral.coordinateCircleDeterminant` | formalized |
| 110 | Cyclic quadrilateral spreads | 184 | `Quadrilateral.cyclic_quadrilateral_spreads`; `Quadrilateral.normalizedCyclicSubtendedSpreads` | formalized |
| 111 | Quadrilateral circumquadrance | 185 | `Quadrilateral.quadrilateral_circumquadrance`; `Quadrilateral.circumquadrance_polynomial_scaled_spread` | formalized |
| 112 | Cyclic quadrilateral quadrea | 187 | `Quadrilateral.cyclic_quadrilateral_quadrea`; `Quadrilateral.cyclicQuadrea_polynomial_identity` | formalized |
| 113 | Cyclic signed area | 188 | `Quadrilateral.cyclic_signed_area`; `Quadrilateral.orientedUnitCirclePoint` | formalized |
| 114 | Ptolemy’s theorem | 190 | `Quadrilateral.ptolemy`; `Quadrilateral.ptolemy_cleared_factorization` | formalized |
| 115 | Four point relation | 191 | `Quadrilateral.four_point_relation`; `Quadrilateral.euler_coordinate_identity` | formalized |
| 116 | Euler line | 193 | `euler_line`; `euler_center_relation`; `euler_center_cleared_coordinates` | formalized |
| 117 | Nine point circle | 195 | `nine_point_circle`; `ninePointCircle` | formalized |
| 118 | Translate of a conic | 198 | `Conic.translate_of_conic`; `Conic.translateConic` | formalized |
| 119 | Tangent to a conic | 200 | `Conic.tangent_to_conic`; `Conic.tangentLine` | formalized |
| 120 | Tangent to a circle | 200 | `Conic.tangent_to_circle` | formalized |
| 121 | Parabola reflection | 201 | `Conic.parabola_reflection` | formalized |

## Chapter detail

### Chapter 1

- The introductory `4,5,7` triangle calculation is
  `ChapterOneExamples.introductory_quadrea`; its exact Archimedes numerator is
  `1536`.  `ChapterOneExamples.exercise_1_1` verifies the preceding value
  `s₁=384/1225` and the two requested values `s₂=24/25` and `s₃=24/49`, with
  every finite denominator justified explicitly.
- Exercise 1.2 asks the reader to inspect elementary and advanced geometry
  books and report whether their definitions of angle support the author's
  criticism.  It is an empirical reading task, not a mathematical proposition
  with a Lean proof obligation.

### Chapter 2

- Theorem 1: formalized with the book's degenerate-case omission corrected.
- Example 2.1 is `ChapterTwoExamples.example_2_1`: both small
  characteristic-seven arithmetic identities and the displayed fraction sum
  are proved exactly, with explicit nonzero certificates for `53` and `17`.
- Example 2.6 is `example_2_6`, stated through the quotient-free
  cross-product equation for `3:7=(12/7):4`.  Examples 2.8–2.10 are
  `example_2_8`, `example_2_9`, and `example_2_10`, including the exact
  trinomial, Fibonacci, and Cauchy identities.
- Example 2.7 is `example_2_7`.  `RFAP.finitePrefixSum` is a project-owned
  primitive recursion that evaluates exactly `n+1` printed terms;
  `RFAP.finite_binomial_theorem` proves the expansion directly from Pascal's
  recursion for `Nat.choose`.  No `Finset`, completed series, or unbounded sum
  enters the proof.
- `alternatingThree` is the source's explicit six-term three-index bracket;
  Examples 2.11–2.14 are its displayed determinant and antisymmetrization
  expansions.  `alternatingFour` and `example_2_15` give the printed 24-term
  four-index expansion directly.  Exercises 2.5–2.7 are `exercise_2_5`,
  `exercise_2_6`, and `exercise_2_7`, all proved as direct finite polynomial
  identities.
- Exercises 2.1–2.2 are `exercise_2_1` and `exercise_2_2`.
  `spreadParameter_isSpreadNumber` displays the square witness for
  `u²/(1+u²)`, while `spreadNumber_has_parameter` constructively recovers
  `u=r/(1-s)` from the witness `s(1-s)=r²`.  The two-input identity uses the
  explicit witness `(x-y)(1+xy)/((1+x²)(1+y²))`; when `xy≠-1`, the requested
  parameter is exactly `(x-y)/(1+xy)`.
- Exercise 2.8 is `exercise_2_8` with the nonzero determinant denominator
  required by its printed root formula; `exercise_2_8_commonRoot_unique`
  proves that formula unique.  The printed unrestricted biconditional is
  false: `exercise_2_8_printed_counterexample` uses the identical rational
  equations `x²+1=0`, whose determinant identity vanishes but which have no
  rational root.
- Exercise 2.9 is corrected by `exercise_2_9`: coincident equations require
  an explicit square witness for `q`, while distinct centers satisfy
  `(p₁-p₂)²=4q`; `exercise_2_9_commonRoot_unique` proves their common root is
  the displayed midpoint.  `exercise_2_9_printed_counterexample` shows that
  the book's `p₁-p₂=±2q` is false already for two rational equations with
  `q=4`.
- `ThreeProportion` and `ThreeProportion.Equivalent` retain the source's
  nonzero data and its three quotient-free cross-product conditions.
  Exercise 2.4 is `exercise_2_4`: three explicit valid pairs show in turn
  that none of those conditions follows from the other two.
- Example 2.18 is `ChapterTwoExamples.example_2_18`, the exact characteristic-
  nineteen factorization `S₅(x)=9x(x-9)²(x-16)²` over an arbitrary
  constructive explicit field.  The three companion `_multiplicity_`
  theorems display the source's polynomial cofactors and prove them nonzero at
  `0`, `9`, and `16`, establishing the stated multiplicities;
  `example_2_18_zeroes` proves these are the only zeroes by branching on just
  those three candidates, without a root search or carrier enumeration.
- Example 2.16 is `ChapterTwoExamples.example_2_16`, identifying `S₅` with
  the exact finite quintic expression plotted by the source.  Example 2.17 is
  `ExampleTwoSeventeen.example_2_17`, a kernel evaluation of the nineteen
  literal input/output labels as two finite lists; it deliberately makes no
  claim that the input list enumerates an ambient carrier.
- Example 2.19: `DivineProportions.example_2_19`.
- Examples 2.2, 2.4, and 2.5 are the seven source tables in
  `FiniteSquareSpreadTables`.  `SquareTableCertified`,
  `SpreadTableCertified`, and `SquareSpreadTableCertified` retain one explicit
  root per printed entry, check every residual, prove the displayed values
  duplicate-free, and check their literal lengths.  In accordance with the
  finite proof boundary, these are witness tables rather than a theorem that
  a list globally enumerates an ambient field carrier.
- The `F₅` row in Example 2.5 is corrected by
  `FieldFive.example_2_5_corrected`: the preceding printed tables themselves
  give squares `{0,1,4}` and spreads `{0,1,3}`, whose intersection is
  `{0,1}`.  `FieldFive.printed_four_radicand` checks directly that the spread
  radicand of `4` is `3`, exposing the erroneous extra printed entry.
- Example 2.3 is retained constructively in
  `ExampleTwoThree.squareNumber_nonnegative`,
  `ExampleTwoThree.spreadNumber_mem_unitInterval`, and
  `ExampleTwoThree.example_2_3`.  The forward order bounds hold over exact
  constructive rationals; the decimal-field converse is stated with the two
  square-root witnesses it analytically presupposes.
- Exercise 2.3 is reduced to its finite algebraic content by
  `squareSpread_iff_unitCircleLift`, `unitCircleLift_sign_choices`, and
  `four_unitCircle_lifts`: square-spread values are exactly first-coordinate
  squares on the unit circle, with four explicit sign choices away from the
  boundary values.  `exercise_2_3_four_mul_add_one` and
  `exercise_2_3_four_mul_add_three` give the resulting `(p+3)/4` and `(p+5)/4`
  arithmetic branches.  The ordinary intermediate claim that a whole finite
  field's unit circle has `p-1` or `p+1` points is intentionally not encoded:
  it is precisely the forbidden global carrier-cardinality step.

### Chapter 3

- Definitions of point, line, null line, incidence, parallelism, and
  perpendicularity: `Point`, `Line`, and the `Line` predicates.
- Theorems 2–7: formalized, including explicit constructions and uniqueness.
- Examples 3.1–3.4: formalized.  Example 3.2 is the closed
  `ExampleThreeTwo.example_3_2` check on the two displayed `F₁₁` points.
  Example 3.4 is explicitly stated in
  characteristic eleven and evaluated in the executable, kernel-verified
  `FieldEleven.Element` model.
- Exercise 3.1: formalized by its displayed parallel-line counterexample.
- Exercise 3.3 is `exercise_3_3`.  From one supplied null line,
  `squareRootNegativeOne_of_nullLine` constructively recovers a square root of
  `-1`; the exercise then constructs the two null directions through any
  requested point, proves them inequivalent when `2≠0`, and proves every null
  line through that point equivalent to one of them.  Thus “exactly two” is
  expressed without enumerating a field carrier or quotienting line triples.
- Exercises 3.4–3.7 are `exercise_3_4` through `exercise_3_7`.
  The explicit `direction_scale_of_parallel` certificate now lives in the
  incidence layer; it proves invariance of perpendicularity under parallel
  representatives and that simultaneously parallel/perpendicular lines are
  null.  `positiveNullLine` and `negativeNullLine` give Exercise 3.6's two
  displayed families directly from a witness `i²=-1`.
- Exercises 3.8–3.9 are `exercise_3_8` and `exercise_3_9`, identifying all
  three printed coefficients with the executable `parallelThrough` and
  `altitudeThrough` constructions applied to `lineThrough`.
- Exercise 3.10 is `exercise_3_10`, the exact two displayed rational
  coordinates obtained by expanding `altitudeFoot` on `lineThrough`; the
  non-null side certificate is the explicit denominator premise.
- Exercise 3.11 is `exercise_3_11`: the three side lines of a displayed
  noncollinear triangle are pairwise nonparallel, and Exercise 3.5 then proves
  constructively that no pair of its three right-vertex conditions can hold.
  Exercise 3.12 is `exercise_3_12`; three explicit null-side certificates
  force all three quadrances to zero and hence collinearity, with the standing
  `2≠0` characteristic premise visible.
- Exercise 3.14 is `ExerciseThreeFourteen.exercise_3_14`.  The displayed
  four-point witness is pairwise distinct and has all four three-point
  determinants nonzero, while its two diagonal `lineThrough` constructions
  are parallel over every constructive field with `2≠0`.
- Exercise 3.15 is `exercise_3_15`.  Its three inner pairs of weights are
  proved to sum to one, and all three cyclic nestings reduce to the same
  explicit `affineCombinationThree`; each denominator is justified solely by
  the source premise that the corresponding outer weight differs from one.
- Exercise 3.16 is `exercise_3_16`.  It constructs the three finite
  `medianLine` witnesses and derives their vertex--midpoint distinctness from
  noncollinearity.  If `3=0`, their explicit coefficient rows are pairwise
  parallel; if `3≠0`, they are pairwise nonparallel and all contain the
  executable `centroidPoint=[(x₁+x₂+x₃)/3,(y₁+y₂+y₃)/3]`.
- Exercise 3.17 is `exercise_3_17`.  The stronger identity
  `midpoint_quadrilateral_side_conditions` proves parallel opposite sides for
  the side midpoints of any four points.  Under the source's nondegenerate
  parallelogram premises, `midpoint_quadrilateral_determinant_ne_zero` retains
  noncollinearity and `midpoint_quadrilateral_same_center` identifies both new
  diagonal midpoints with the original center.
- Example 3.5: evaluated exactly in `F₁₁`, including the proportional altitude
  representative and foot `[2,9]`.
- Example 3.6 is `ExampleThreeSix.example_3_6`: under the literal
  characteristic-thirteen equation, `⟨6:4:1⟩` contains `[5,2]`, is both
  parallel and perpendicular to the null line `⟨3:2:1⟩`, and is equivalent
  to the executable altitude construction.  Example 3.7 is
  `ExampleThreeSeven.example_3_7`, proving the three printed points
  noncollinear and checking all six printed point--line incidences by exact
  characteristic-thirteen polynomial identities, without a carrier model.
- Example 3.8: formalized as its exact one-third/two-thirds coordinate formula.
- Exercise 3.2 is represented without carrier enumeration by
  `ChapterThreeCounting.exercise_3_2_lines_through_point` and
  `ChapterThreeCounting.exercise_3_2_points_on_line`.  The first gives a
  complete, disjoint chart consisting of one normalized line for every
  supplied slope plus the vertical line.  The second selects a nonzero line
  coefficient and constructs an injective, covering one-scalar
  parametrization of all incident points.  These are the explicit bijection
  data behind the source's `p+1` and `p` counts.
- Exercise 3.13 is retained at the same finite boundary in
  `ExerciseThreeThirteen`.  `triangle_count_cleared` proves that subtracting
  the collinear-triple numerator from the all-point-triple numerator gives
  `p³(p-1)(p²-1)`, hence the usual count `p³(p-1)(p²-1)/6` recorded by
  `triangleCount`.  `null_triangle_count_cleared` performs the null-side
  incidence count and subtracts the twice-counted two-null-side triangles,
  giving `p²(p-1)³` when `-1` has a square root and zero otherwise.  The
  source's global finite-cardinality phrasing is deliberately replaced by
  these charts and cleared integer identities.

### Chapter 4

- Theorems 13–17: formalized from the geometric altitude-foot definition
  through homogeneous reflection composition and lineation composition.
- Theorem 18 is `cyclic_reflection_right` and `cyclic_reflection_left`.
  `ReflectionPair`, `reflectionPairAt`, and `reflectionLineAt` replace the
  source's completed two-sided sequence by an executable iterator.  For any
  requested center and finite offset, the two theorems prove both orientations
  of the displayed reflection symmetry on exactly that computed window; their
  two-step induction is the source proof through Lineation and involutivity.
- Exercise 4.2 is `exercise_4_2`.  `SuccessiveRotationPair` and
  `successiveRotationPairAt` replace its completed two-sided point sequence by
  a finite iterator.  `successiveRotationPointAt_formula` proves the exact
  arithmetic-progression coordinates, and the exercise gives both directions
  of `ρ_{Aₖ}(Aₗ)=A_{2k-l}` on every requested finite symmetric window.
- Exercises 4.1, 4.3, and 4.5: formalized (`rotateInPoint_affine`,
  `reflectPoint_affine`, and `reflectLine_involutive`).
- Exercise 4.4: corrected.  Its forward implication is formalized, while
  `reflectLine_self_equivalent` and `reflectLine_self_not_perpendicular` prove
  that the printed converse omits the fixed mirror line.
- Exercise 4.6: refuted as printed.  `null_reflection_formula_self_zero` proves
  that a null mirror reflected in itself gives the forbidden zero coefficient
  triple, so the formula does not always “make sense” as a line.
- All Chapter 4 exercises and numbered theorems are formalized, subject to the
  recorded corrections to Exercises 4.4 and 4.6 and the finite-prefix
  treatment of Exercise 4.2 and Theorem 18.

### Chapter 5

- Theorems 19–32 are formalized over an arbitrary constructive
  `RFAP.ExplicitField`; the midpoint, Triple-quad, and Pythagoras statements
  expose the source's necessary `2 ≠ 0` hypothesis.
- Example 5.1 is made fully finite and executable in `F₅`:
  `example_5_1_fieldFive` and `example_5_1_fieldFive_distinct` verify that the
  distinct points `[0,0]` and `[1,2]` have zero quadrance.
- Example 5.2 is the closed certificate `ChapterFiveExamples.example_5_2`.
  It checks the three printed `F₁₁` points, all six side-line incidences, the
  right vertex, quadrances `9,1,10`, and their Pythagorean relation by kernel
  computation.
- Exercise 5.1 is `exercise_5_1`, the exact printed quotient for the
  quadrance between `l₁l₂` and `l₁l₃`.  Its stronger finite core
  `exercise_5_1_cleared` multiplies through the two squared line-intersection
  denominators and identifies the six-term numerator with
  `lineDeterminant`; the quotient theorem cancels only the two supplied
  nonparallel certificates.
- Theorem 28 is constructive in a stronger, executable sense: every
  sum-of-two-squares and nonzero-square premise carries an explicit witness,
  and the proof constructs the triangle coordinates by a finite three-way
  case split over the nonzero quadrance.
- Exercise 5.2 is `exercise_5_2`.  The finite affine centroid decomposition
  gives the exact median quadrance factors `4/9` and `1/9`, with explicit
  `2≠0` and `3≠0` denominator certificates.
- Exercises 5.4--5.6 are `exercise_5_4`, `exercise_5_5`, and
  `exercise_5_6`.  `segmentDirectionDot`, `IsRectangle`, and
  `IsRhombus` retain the source's rectangle and rhombus definitions as finite
  coordinate dot products and a displayed parallelogram certificate;
  `segmentDirectionDot_eq_zero_iff_perpendicular` identifies them with the
  corresponding displayed-line relation.  The shared constructive lemma
  `parallelogram_coordinate_sums` supplies the exact coordinate equalities
  used in the source proof.  Thus equal diagonals characterize rectangles,
  the diagonal sum is twice the adjacent-side sum, and four equal sides
  characterize perpendicular diagonals without choosing roots or directions.
- Exercise 5.7 is `exercise_5_7`, retaining all five printed forms of
  Archimedes' function, including explicit two-by-two and four-by-four finite
  determinant expansions.  Exercises 5.8 and 5.10 are `exercise_5_8` and
  `exercise_5_10`: the four
  signed linear relations give explicit quad triples, and Archimedes'
  relation is expanded as the printed quadratic in its third entry.
  Exercise 5.11 is `exercise_5_11`, with the necessary distinct-centre
  premise inherited from the corrected Quadratic compatibility theorem.
- Exercise 5.9 is the closed constructive-rational theorem
  `ExerciseFiveNine.exercise_5_9`.  `IsSquaredSumTriple` treats the source's
  braces literally up to all three choices of the `(a+b)²` entry.  The explicit
  quad triple `{3,3,12}` cannot have that form because the computable reduced-
  fraction certificate `square_ne_three` rules out the required rational
  square root, without completed reals or an unbounded search.
- Exercise 5.12 is `exercise_5_12`: nonzero quadrea forces both quadrances
  adjacent to a right vertex to be nonzero.  The requested counterexample for
  the opposite quadrance is `ExerciseFiveTwelveExample.opposite_quadrance_can_vanish`,
  an exact noncollinear right triangle in `F₅`.
- Exercise 5.13 is `ExerciseFiveThirteen.exercise_5_13`.  Its scalar core
  `exercise_5_13_scalar` replaces the source's informal maximum with the
  pointwise constructive-rational bound
  `A(Q₁,Q₂,Q₃) ≤ 4Q₁Q₂`; equality holds exactly when
  `Q₁+Q₂=Q₃`, and Pythagoras identifies that equality case with a right
  vertex.  No supremum, limiting process, or completed decimal field is used.
- Exercises 5.14–5.15 are `exercise_5_14` and `exercise_5_15`, both direct
  finite polynomial expansions of the quadrea.  Exercise 5.18 is
  `exercise_5_18`; cancellation of the explicit nonzero factor `a-c`
  constructs the common value `(a+c-2b)/2`.
- Exercise 5.16 is `exercise_5_16`, with the denominator-cleared core
  `exercise_5_16_cleared`.  The reusable finite duality identity
  `lineTriangle_pointDeterminant_cleared` proves that the point determinant
  of `l₂l₃`, `l₃l₁`, and `l₁l₂`, multiplied by the three explicit
  intersection denominators, is the square of the line determinant.  Its
  square yields the printed fourth-power quadrea numerator, after which only
  the three supplied nonparallel certificates are cancelled.
- Exercise 5.3 is corrected by `exercise_5_3_corrected`.  A supplied square
  root of `-1` gives an explicit sum-of-two-squares representation of every
  field scalar, but Theorem 28 still requires the Archimedes function to be a
  nonzero square.  The printed claim omits this condition:
  `exercise_5_3_printed_counterexample` proves that the nonzero triple
  `(1,1,4)` has zero quadrea and therefore cannot be realized by a triangle.
- Exercise 5.17 is retained at the finite counting boundary in
  `ExerciseFiveSeventeen`.  `completionPoint_quadrances` proves the displayed
  completion formula, `completionPoint_not_collinear` certifies that a
  nonzero area root produces an actual triangle, and
  `exercise_5_17_two_completions` proves that its two signs give two distinct
  triangles.  The arithmetic declarations `countFourMulAddThree` and
  `countFourMulAddOne` combine this factor two with supplied `p²` translation
  and `p+1` or `p-1` nonzero-circle factors.  As in the Chapter 3 counting
  exercises, no global list of all field elements or triangles is introduced.
- Exercise 5.19 is `ExerciseFiveNineteen.exercise_5_19_quintuple`, with
  `QuintupleQuadRelation` displaying the two diagonal witnesses and the three
  successive quad triples.  `FiniteQuadRelation` is its primitive-recursive
  generalization for any requested finite list, and
  `exercise_5_19_general` proves it for every explicitly closed finite chain
  of signed increments.
- All Chapter 5 numbered theorems, examples, and exercises are formalized,
  subject to the correction to Exercise 5.3 and the explicit finite-counting
  boundary for Exercise 5.17.

### Chapter 6

- The finite ratio primitives `spread`, `cross`, and `twist` use explicit
  nonzero-denominator certificates.
- Theorems 33–44 are formalized.  The converse half of Theorem
  34 constructs two concrete non-null lines from the supplied square witness,
  over an arbitrary nontrivial explicit field.
- The ratio statements retain the book's exact quotient forms, with every
  cancellation justified by a non-null line or explicit `2 ≠ 0` premise.
- Theorem 45 is formalized in full by `vertex_bisector`: its two normalized
  witnesses are explicit, distinct, perpendicular, and exhaustive up to line
  equivalence, and existence is equivalent to the original spread being a
  square.  Theorem 46 is the factorized locus theorem
  `equal_pointLineQuadrance_iff_on_vertexBisector`.
- Examples 6.5 and 6.6 are evaluated over the executable constructive
  rational field in `ChapterSixExamples.ExampleSixFive.example_6_5` and
  `ChapterSixExamples.ExampleSixSix.example_6_6`, including the displayed
  line representatives and all four stated spread values.
- Example 6.1 is the exact constructive-rational certificate
  `ChapterSixExamples.ExampleSixOne.example_6_1`, including quadrea `455`
  and all three unreduced spread quotients.  Example 6.2 is
  `ExampleSixTwo.example_6_2`: the reduced-fraction theorem `square_ne_455`
  uses only five literal remainder cases to rule out the square required by
  Triangle quadrea, and hence rules out the requested rational triangle.
- Example 6.3 is `ExampleSixThree.example_6_3`.  The explicit `F₁₁` points
  `[0,5]`, `[2,1]`, and `[0,0]` realize quadrances `5,3,9`; their determinant
  is certified nonzero and their three spreads evaluate to `9,1,3` without
  enumerating the field.  Example 6.4 is `ExampleSixFour.example_6_4`,
  parameterized over an arbitrary explicit field by the one requested witness
  `i²=-1`; it proves quadrea `6i` and spreads `3/4,3/2,3i/4` without a
  completed complex carrier.
- Exercise 6.1 is `exercise_6_1`, proving all six printed conversions among
  spread, cross, and twist.  Its proof derives the nonzero `1+t` denominator
  from the explicit identity `c(1+t)=1`; no field denominator is silently
  cancelled.  Exercise 6.2 is the closed constructive-rational certificate
  `ExerciseSixTwo.exercise_6_2`: the directions `(4,3)` and `(3,4)` have
  complementary spreads `16/25` and `9/25` with `(0,1)`, but coefficient dot
  product `24`, so the first two lines are not perpendicular.
- Exercise 6.3 is `exercise_6_3`: the three cyclic Quadrea-spread equations,
  with their explicit nonzero quadrances, give the full printed chain through
  `A/(4Q₁Q₂Q₃)`.  Exercises 6.4 and 6.5 are `exercise_6_4` and
  `exercise_6_5`; direct specialization to one or two zero quadrances proves
  the negative-square formulas, and the Exercise 6.4 spread quotient cancels
  only `4Q₁Q₂≠0`.
- Exercise 6.6 is the pointwise constructive-rational inequality
  `ExerciseSixSix.exercise_6_6`.  Its nonnegative residual is exactly
  `4 * pointDeterminant²` by the Quadrea theorem, so the proof uses neither
  square roots nor a completed ordered field.
- Exercise 6.7 is `exercise_6_7`, the exact point-coordinate twist formula
  corresponding to Theorems 43 and 44; it unfolds only the two executable
  `lineThrough` coefficient triples.  All Chapter 6 reader exercises are now
  formalized.
- All numbered theorems, examples, and reader exercises in Chapter 6 are now
  formalized within the finite constructive boundary.

### Chapter 7

- Theorems 47–51 are formalized over arbitrary constructive explicit
  fields by `triple_spread_formula`, `spread_from_ratio`,
  `triple_cross_formula`, and `equal_spreads`.  Theorem 47 is proved directly from the six finite line
  coefficients with one explicitly cancelled common denominator.
- Theorems 52–55 are `spread_reflection`, `two_spread_triples`,
  `quadruple_spread_formula`, and `quadruple_cross_formula`; their proofs use
  explicit finite factorization and the audited quadratic-compatibility API.
- The triple-spread function, spread-triple predicate, and the displayed
  four-by-four determinant are `tripleSpreadFunction`, `SpreadTriple`, and
  `tripleSpreadDeterminant`.
- Exercises 7.1–7.3 and 7.6 are formalized as `exercise_7_1`, `exercise_7_2`,
  `spreadTriple_zero_iff`, `spreadTriple_one_iff`, and `exercise_7_6`.
- Exercise 7.4 is `ChapterSevenInequalities.exercise_7_4`.  Factoring the
  equal-argument polynomial as `a²(3-4a)` gives the exact constructive-rational
  equivalence with `a≤3/4`, using only explicit quotient-order cancellation.
- Exercise 7.5 is `exercise_7_5`: its two displayed rational parameters are
  reduced to one common finite denominator with both cancellations explicit.
  `exercise_7_5_counterexample` supplies the requested non-parametrized
  spread triple `{1,0,1}` over every nontrivial constructive explicit field.
- Exercises 7.7 and 7.8 are `exercise_7_7` and `exercise_7_8`; they give both
  printed Triple-cross normal forms and the expanded four-by-four determinant
  identity.  Exercises 7.10 and 7.11 are `exercise_7_10` and `exercise_7_11`,
  including the cleared quadratic and completed-square normal forms of the
  Triple-twist equation.
- Exercise 7.12 is `exercise_7_12`; its cyclic turn identity is
  `triple_turn_formula`, which also formalizes the line statement of the
  later Theorem 61.
- Exercise 7.13 is `exercise_7_13`: subtracting the two adjacent spread-triple
  equations produces the exact printed quotient, with characteristic two and
  both possible zero factors handled explicitly.
- Exercise 7.9 is false as printed.  The fully executable rational triangle
  `(0,0),(1,0),(2,1)` is certified non-collinear in
  `ExerciseSevenNineCounterexample.triangle_certificate`; its three crosses
  are `4/5`, `1/2`, and `9/10`.  Thus both the claimed product bound and the
  claimed `5/4` upper sum bound are refuted by `product_bound_fails` and
  `sum_bound_fails` rather than silently assumed.
- Example 7.2 is the exact constructive-rational calculation
  `ChapterSevenExamples.ExampleSevenTwo`: the three displayed lines,
  incidences, quadrances, quadrea, spreads, crosses, and both triple formulas.
  Example 7.3 is the fully executable eleven-element-field calculation
  `ChapterSevenExamples.ExampleSevenThree.example_7_3`, with its displayed
  triple-spread value checked separately by `triple_spread_value`.
- Example 7.1 is `ChapterSevenFieldFragments.ExampleSevenOne.cross_values`
  and `triple_cross_value`.  It uses only a supplied field element `i` with
  `i²=-1`, proves all three Cross-law quotients, and checks that both sides of
  the Triple-cross formula are `25/16`.
- Example 7.4 is the complete geometric and arithmetic certificate in
  `ChapterSevenFieldFragments.ExampleSevenFour`: the three displayed points
  and side lines, all six incidences, quadrances, quadrea, spreads, common
  Spread-law value, twists, and both sides of the Triple-spread and
  Triple-twist formulas.  `AdmissibleCharacteristic` exposes exactly the six
  small prime-characteristic exclusions needed by its printed denominators;
  consequently the proof applies to the constructive Gaussian rationals and
  to every admissible finite-field fragment without constructing a completed
  complex carrier.
- Exercise 7.14 is false as printed: complementing the four adjacent spreads
  preserves the quadruple polynomial but changes each diagonal quotient to
  `1 - quotient`.  `ExerciseSevenFourteenCounterexample` checks this in
  `F₁₁` using the four lines `⟨1:0:0⟩`, `⟨1:1:0⟩`, `⟨0:1:0⟩`, and
  `⟨1:2:0⟩`: the first printed right-hand side is `1`, while `c₁₃=0`.
  `exercise_7_14_corrected` proves both valid complemented formulas with their
  exact nonzero-denominator hypotheses.
- Exercise 7.15's open-ended request is answered without inventing an
  unspecified eliminated polynomial.  `finiteSpread`,
  `finite_spread_triples`, and `finite_quadruple_spread_relations` give the
  bounded compatibility system for an arbitrary `Fin n` family of non-null
  lines; `exercise_7_15` specializes the full bounded family of necessary
  relations to five lines.
- All numbered theorems, examples, and reader exercises in Chapter 7 are now
  formalized, with the two false printed claims recorded explicitly.

### Chapter 8

- `spreadPolynomial` is a primitive-recursive, executable finite definition.
  Theorems 56, 57, and 59 are `three_equal_spreads`, `recursive_spreads`, and
  `spread_polynomial_formula`; the latter is first proved in the
  denominator-cleared form `spread_polynomial_formula_cleared`.
- Theorem 60 is `spread_polynomial_composition`.  Its proof replaces the
  source's infinite reflection sequence and density/root-counting step by the
  characteristic-free finite recurrence identity
  `spread_polynomial_addition`.  The stated commutativity and associativity
  consequences are `spread_polynomial_composition_commutative` and
  `spread_polynomial_composition_associative`.
- Theorem 58 is `consecutive_spreads`.  It reuses Theorem 18's executable
  finite state `ReflectionPair` and primitive recursion `reflectionPairAt`;
  requesting index `n` constructs exactly `n` reflection steps.
  `reflectionLineAt_succ_succ` records the printed recurrence and
  `reflectionLineAt_adjacent_spread` proves its finite invariant.
- Example 8.5 is formalized over an arbitrary constructive explicit field in
  `ChapterEightExamples`: its displayed cubic and quintic formulas and both
  factorizations of `S₁₅` and `S₃₀` are checked exactly.
- Exercise 8.1 is `exercise_8_1`: after substituting the selected three-step
  branch into one Triple-spread equation, its two requested results are the
  two explicit factors of a quadratic.
- The unnumbered list `S₀,…,S₇` is checked in expanded and factored form by
  `ChapterEightExamples.spreadPolynomial_two` through
  `spreadPolynomial_seven`.
- Examples 8.1–8.4 are the executable certificates in
  `ChapterEightFiniteFieldExamples`.  The new explicit kernel fields `F₇`,
  `F₁₃`, and `F₁₉` use complete inverse tables rather than the general
  finite-field hierarchy.  `HasSpreadOrder` checks minimality over a bounded
  `Fin (n-1)` carrier; all printed spread-number classifications, orbit lists,
  and the full `F₅` and `F₇` tables are certified.  The arbitrary-index
  period claims follow constructively from `spreadPolynomial_period` once
  two consecutive finite seeds have been checked.
- `crossPolynomial` is the source's primitive recursion.  Exercises
  8.14–8.19 are `exercise_8_14`, `exercise_8_15`,
  `cross_polynomial_composition`, `exercise_8_17`,
  `crossPolynomial_even_and_odd`, `exercise_8_19_cross`, and
  `exercise_8_19_spread`.  The constructive bridge
  `crossPolynomial_eq_one_sub_spreadPolynomial` proves
  `Cₙ(c)=1-Sₙ(1-c)` for every requested finite index and drives the
  composition, parity, and doubling proofs.
- `chebyshevFirst` is the finite first-kind Chebyshev recurrence.
  `exercise_8_4_cleared` proves `2Sₙ(s)=1-Tₙ(1-2s)` without division, and
  `exercise_8_4` recovers the source's `/2` form under the exact
  characteristic-two exclusion.  This is the complete polynomial content of
  Exercise 8.4; its alternative completed-decimal square-root notation is
  deliberately not introduced.
- `chebyshevFirst_square_invariant` is the finite identity
  `Tₙ(x)²+(1-x²)Uₙ₋₁(x)²=1`.  Exercise 8.3 is
  `ExerciseEightThree.exercise_8_3`: over the project-owned constructive
  rational field, this identity proves `0≤Sₙ(s)≤1` whenever `0≤s≤1`, for
  each requested finite `n`.  The source's completed decimal-field clause is
  deliberately outside the finite boundary.
- `spreadBinomialExpansion`, `exercise_8_6_even`, and `exercise_8_6_odd`
  are Exercise 8.6's exact alternating even-binomial formula, including its
  two printed terminal terms.  `RFAP.QuadraticPair K b` is an executable
  two-coordinate ring with `j²=-b`; it makes the source's binomial argument
  work over every admissible field without selecting either square root or
  constructing a completed extension.  All sums are primitive-recursive
  finite prefixes.
- `oddSpreadRootExpansion` and `ExerciseEightSeven.exercise_8_7` prove
  Exercise 8.7 for every finite odd index `n=2l+1`: `Sₙ(s)` is `s` times
  the square of the exact displayed odd-binomial prefix, whose last term is
  `(-s)^l`.  The proof uses two nested finite quadratic-pair rings to retain
  the source's binomial argument without assuming either square root exists
  in the coefficient field.
- `borderedSpreadEntry` encodes Exercise 8.8's complete finite
  bordered-tridiagonal matrix family.  `symmetricContinuant` and
  `borderedSpreadDeterminant` give its cofactor evaluation, and
  `exercise_8_8` proves it is `Sₙ(s)` in every requested dimension.  The
  separate `exercise_8_8_first_four` checks the source's four literal
  determinant displays through explicit two-, three-, and four-row
  expansions.
- `spreadArrayCoefficient` is the shifted-Pascal entry underlying Exercise
  8.9.  `exercise_8_9_integer_coefficients` proves the displayed finite
  expansion in the stronger division-free form over every commutative ring;
  `exercise_8_9` recovers the book's descending-index quotient notation under
  exactly the finitely many nonzero natural-cast premises it uses.
  `spreadArray_first_four_rows` certifies the printed rows through
  `[16,20,8,1]`, and `scaledSpreadPolynomial_three` checks the worked
  `S₃*(r)=9r-6r²+r³` example.  No polynomial completion or unbounded
  coefficient family is introduced.
- Exercise 8.10's infinite series is retained at the agreed finite boundary.
  `spreadGeneratingPrefix` computes exactly the first requested positive-index
  terms, and `exercise_8_10_finite` proves that multiplying this prefix by the
  source denominator `(1-x)³+4sx(1-x)` gives `sx(1+x)` plus the complete
  three-term boundary remainder in degrees `N+1`, `N+2`, and `N+3`.  Thus
  every finite coefficient claimed by the generating-function calculation is
  certified without introducing a completed series.
- `scaledSpreadCoefficientExpansion_cleared` proves the division-free scaling
  law behind Exercise 8.20.  `exercise_8_20_even` and
  `exercise_8_20_odd` then give the complete rule for reading scaled cross
  coefficients from the spread array: odd rows retain the alternating row,
  while even rows subtract it from the constant `4`.
  `scaledCrossPolynomial_first_four` checks the resulting rows through
  `4-16r+20r²-8r³+r⁴`.
- The field-independent reduction in Exercise 8.2 is
  `ExerciseEightTwo.exercise_8_2_from_finite_seeds`: the two values at the
  proposed finite period seed every later equality through the already proved
  second-order recurrence.  `RFAP.QuadraticPair.prime_add_pow` lifts the
  finite prime-binomial law to the executable two-coordinate quadratic ring.
  `ExerciseEightTwo.prime_chebyshev_period_seeds` uses its two norm-one
  conjugates to prove both required seeds, with decidable equality selecting
  only the discriminant-zero and two Euler-value cases.
  `ExerciseEightTwo.exercise_8_2_prime_residue` therefore proves the complete
  period `Sₙ₊ₖ(r)=Sₙ(r)`, `k=(p-1)(p+1)/2`, for every natural residue label in
  an odd prime characteristic.  No field carrier, global enumeration, or
  cardinality argument is introduced.
- `RFAP.prime_interior_natCast_ne_zero` uses the executable extended Euclidean
  algorithm to certify every nonzero natural cast below `p`.
  `RFAP.prime_interior_choose_cast_zero` then uses Pascal's finite
  multiplicative recurrence, and `RFAP.prime_add_pow` proves the prime-binomial
  law by an explicitly bounded prefix.  Finally,
  `RFAP.prime_natCast_pow` derives Frobenius for every natural residue label.
  `ExerciseEightFive.spreadBinomialExpansion_prime_odd` then collapses the
  finite expansion from Exercise 8.6, and
  `ExerciseEightFive.exercise_8_5_prime_residue` proves Exercise 8.5 uniformly:
  in characteristic `p`, `Sₚ(r)=r` for every natural residue label `r`.
  The theorem needs no global finite-field carrier, enumeration, cardinality,
  or completed object.  `exercise_8_5_from_frobenius` remains as the more
  abstract pointwise reduction.
- Exercise 8.11's requested bounded sum is
  `ExerciseEightEleven.finiteSpreadInnerProduct`; its exceptional answers are
  recorded exactly as `-1/16` and `1/16`, with their division-free
  characterizations in `exceptional_values_cleared`.
  `RFAP.prime_power_sum_zero_below`, `RFAP.prime_power_sum_fermat`, and
  `RFAP.prime_power_sum_zero_above` establish the required explicitly bounded
  residue power sums by finite differences and one Fermat reduction.
  `prime_centered_chebyshev_moment_zero` and
  `prime_centered_chebyshev_moment_boundary` lift these calculations through
  the two-step Chebyshev recurrence, while
  `finiteCenteredChebyshev_product_sum` proves the finite product-to-sum
  identity.  Exercise 8.5 supplies the pointwise reflection across index
  `p`.  The three resulting cases are
  `finiteSpreadInnerProduct_zero`,
  `finiteSpreadInnerProduct_lower_exceptional`, and
  `finiteSpreadInnerProduct_upper_exceptional`; `exercise_8_11` packages the
  complete statement for `1 ≤ m,n ≤ p-2`.  Every sum is primitive-recursive
  over the natural residue labels `0,…,p-1`; no field carrier or polynomial
  completion is enumerated.
- Exercise 8.12 is retained at the agreed finite boundary.
  `ExerciseEightTwelve.exercise_8_12_integrand_cleared` proves the exact
  centered-spread/Chebyshev numerator identity for every two requested finite
  indices, and `exercise_8_12_integrand` recovers the source's `/2` notation.
  The completed-real weighted integral and the constant `π` are deliberately
  not introduced.
- Exercise 8.13's nine printed integer-coefficient factors are
  `ExerciseEightThirteen.cyclotomicOne` through `cyclotomicTwelve`.
  `exercise_8_13_first_eight` checks every displayed divisor product through
  index eight, while `exercise_8_13_twelve` proves the worked six-factor
  decomposition of `S₁₂`.  The book presents the general assertion as an
  exercise, but it was in fact the Goh--Wildberger conjecture and was first
  proved by Cigler--Herbig in 2026.  The constructive reduction is now
  formalized: `RFAP.finiteTotient` is the literal bounded coprime count,
  `RFAP.finiteDivisorQuotientTotientSum_eq` proves its finite gcd-fibre sum,
  `finiteLucas_product_add_sub_doubled` proves Lucas product-to-sum, and
  `finiteLucas_odd_square_identity`, `finiteLucas_even_square_identity`,
  `spread_odd_lucas_square_cleared`, and
  `spread_even_lucas_square_cleared` prove the two square-multiplicity
  reductions without roots or completed fields.  At coefficient level,
  `IntegerPolynomial.finiteLucasCoefficients` is an executable ascending
  integer list; `eval_finiteLucasCoefficients`,
  `finiteLucasCoefficients_length`, and `finiteLucasCoefficients_monic` prove
  its evaluation, exact slot count, and leading coefficient.  The general
  assertion is now fully finite and executable.  The ordinary factors
  `RFAP.FiniteCyclotomic.finiteCyclotomicCoefficients` are constructed by
  bounded monic long division with integer coefficients.  Their quadratic
  trace norms give
  `IntegerPolynomial.spreadCyclotomicFactorCoefficients`; the complete
  quotient-coordinate product is
  `spreadCyclotomicDivisorProductCoefficients`.  Theorem
  `exercise_8_13_general` proves `S_n` equals this divisor product for every
  positive finite `n` in every explicit field, including finite
  characteristic.  The characteristic-independent core is the integer
  coefficient identity `ofAscending_spreadCyclotomic_factorization`, and
  `spreadCyclotomicFactorPolynomial_natDegree` proves that the factor at
  index `n` has exact degree `RFAP.finiteTotient n`.  No noncomputable
  complex-root cyclotomic development is imported.

### Chapter 9

- Oriented polygons are finite point lists.  `polygonDoubleSignedArea` is the
  denominator-free cyclic shoelace sum, while `polygonSignedArea` is its
  `/2` normalization.  Theorem 62 is `signed_area`, with the explicit
  independence statement `fan_signed_area_independent` and the finite
  telescoping core `fan_double_signed_area`.
- `triangle_quadrea_eq_sixteen_signed_area_square` and
  `polygon_quadrea_eq_sixteen_signed_area_square` prove the book's `16a²`
  normalization under the visible hypothesis `2 ≠ 0`.
- Theorem 63 is the direct four-point polynomial identity
  `bretschneider_formula`.  Exercises 9.4 and 9.5 are `exercise_9_4` and the
  stronger arbitrary-center fan identity `exercise_9_5`.
- Exercise 9.1 defines the finite quotient `coturn` and is proved by
  `exercise_9_1`.  Its denominator-free core
  `triple_coturn_formula_cleared` is the source's six-coefficient polynomial
  identity; only the three displayed nonparallel certificates are used to
  cancel the quotient denominators.  `coturn_reverse` records orientation
  reversal.
- Exercise 9.2 is `exercise_9_2`; its printed equal-turn deduction is
  `exercise_9_2_equal_turns`.  `turnComposition u v = (u+v)/(1-uv)` names its
  rational addition law, and `turn_reverse` supplies the oriented reversal
  used to derive it from `triple_turn_formula`.  The source's tacit nonzero
  composition denominator is explicit because it can fail over finite fields
  admitting null directions.
- `polygon_double_signed_area_split` proves the denominator-free diagonal
  decomposition in Exercise 9.6 for arbitrary finite vertex lists; the
  source's size bounds are needed only to name the two displayed polygons.
  `exercise_9_6` gives its signed-area normalization.  Exercise 9.7 is
  `exercise_9_7`: a direct reversal of the cyclic edge recursion negates the
  signed area, with `polygon_double_signed_area_reverse` as its cleared core.
- Exercise 9.3 is `exercise_9_3_finite_iteration`.  `turnRationalPair n u`
  computes the two coordinates of `(1+ju)ⁿ` in the executable pair ring
  `j²=-1`; its imaginary and real coordinates are respectively the numerator
  and denominator of `turnRationalFunction`.  The coordinate recurrences are
  exactly one `turnComposition`, so Theorem 9.2 identifies this finite
  iterator with every requested equal-turn chain wherever the displayed
  rational denominators are nonzero.  `exercise_9_3_first_five` proves all
  five printed fractions.  `exercise_9_3_even` and `exercise_9_3_odd` give
  the general answer as explicitly bounded alternating odd- and even-binomial
  prefixes, proved by the project-owned finite binomial theorem.
- All numbered theorems and reader exercises in Chapter 9 are now formalized
  within the finite constructive boundary.

### Chapter 10

- Theorem 64 is `null_isosceles`: for a displayed equal pair `Q₁ = Q₂`,
  noncollinearity forces either exactly those two quadrances to vanish or all
  three to be nonzero.
- Theorem 65 is the finite cancellation equivalence `pons_asinorum`, stated
  directly for the four nonzero ratios supplied by a non-null triangle's
  Spread law.
- Theorem 66 is `isosceles_triangle`; its two displayed formulas follow from
  the Spread law and Equal spreads identities with every cancelled scalar
  passed explicitly.
- Theorem 67 is `isosceles_median`.  A cevian is displayed by its vertex and
  intersection with the opposite side; altitude, midpoint intersection, and
  equal vertex spreads are proved equivalent.  The converse bisector argument
  clears its finite spread denominator and uses noncollinearity to exclude the
  external-bisector factor.
- Theorem 68 is the cleared Spread-ratio calculation
  `isosceles_reflection`.  Theorem 69 is `equilateral_triangle`, including
  the common spread `3/4`, cross `1/4`, and quadrea `3Q²`.
- Theorem 70 is the geometric equivalence `right_midpoint`; its finite
  denominator-cleared core is `median_quadrance_cleared`.
- Theorem 71 is `median_triangle`.  Its three midpoint-side quadrances and
  three Thales parallelisms are explicit, and its similarity conclusion is
  witnessed constructively by non-null certificates and all three
  corresponding spread equalities.  The sole characteristic boundary is the
  visible hypothesis `2 ≠ 0`.
- Exercise 10.2's two quadrea factorizations are `exercise_10_2`.
- `ScalarTriple.SameEntries` records the six finite side matches intended by
  the source's unordered congruence and similarity definitions.
  `NonNullTriangle` retains the three vertices, noncollinearity, distinctness,
  and exactly the three non-null side certificates needed to form its finite
  spread triple.  `congruent_triangles_are_similar` proves the intervening
  source claim from three denominator-cleared Quadrea--spread equations,
  without quotienting triangles by permutations.
- Exercise 10.7 is `ChapterTenExamples.ExerciseTenSeven.exercise_10_7`.
  The two literal rational coordinate triples have opposite-side quadrances
  `(50,65,5)` and `(65,50,5)`, with the exchange explicit in the congruence
  witness.
- Exercise 10.8 is `ChapterTenExamples.ExerciseTenEight.exercise_10_8`.
  Its literal triangles have quadrance triples `(65,13,104)` and
  `(416,260,52)`, while their spread triples are respectively
  `(1/2,1/10,4/5)` and `(4/5,1/2,1/10)`.  Thus the finite permutation witness
  proves similarity, and direct reduced-fraction certificates rule out every
  congruence permutation.
- Exercise 10.9 is `NonNullTriangle.exercise_10_9`.  The common Spread-law
  quotient of each triangle supplies the explicit nonzero scale; the six
  similarity constructors give the same six possible matches of the scaled
  quadrances.
- Exercise 10.1 is `exercise_10_1`.  Complementing the Equal-spreads identity
  gives `c₃=(2c-1)²`; substituting the two finite twist quotients gives
  `t₃=4t/(1-t)²`, with the two nonzero crosses exposing exactly when the
  displayed twists are defined.
- Exercise 10.3 is `exercise_10_3`.  If the equal pair of an isosceles
  triangle is null, noncollinearity makes the third quadrance nonzero and its
  quadrea is the negative square of that quadrance.  This records why the
  spread conclusions, whose denominators are the null sides, are unavailable.
- Exercise 10.4 is `exercise_10_4`: for an equilateral triangle the three
  displayed median and centroid quadrances are exactly `q/3`, `q/12`, and
  `3q/4`.  Exercise 10.5 is `exercise_10_5`, proving constructively that a
  unit equilateral triangle exists exactly when `3` has a displayed nonzero
  square root.
- Exercise 10.6 is corrected by `exercise_10_6_corrected`.  With the book's
  convention `Q₁=Q(A₂,A₃)` and `Q₂=Q(A₁,A₃)`, its first two printed
  numerators are interchanged: the correct altitude-foot quadrances are
  `Q₂²/Q₃`, `Q₁²/Q₃`, and `Q₁Q₂/Q₃`.
  `ExerciseTenSix.exercise_10_6_printed_counterexample` checks the rational
  right triangle `[3,0]`, `[0,4]`, `[0,0]`, where the first printed value is
  `256/25` but the actual value is `81/25`.
- Example 10.1 is `ExampleTenOne.example_10_1`.  The cleared Cross law factors
  as `(13Q₂-72)(Q₂-26)=0`, yielding exactly the two displayed rational
  candidates `72/13` and `26`; both Cross-law equations and both complete
  Spread-law quotient chains are then certified by exact rational arithmetic.
- Exercise 10.10 is `FieldThree.exercise_10_10`.  Every noncollinear triangle
  over the executable three-element field is first turned into a
  `NonNullTriangle`; finite scalar certificates then show that every spread
  triple is a permutation of `(2,2,1)` and that every triangle has a displayed
  right-isosceles vertex.  Hence any two such triangles are similar.
  `ExerciseTenTen.representative` checks the literal points `[0,0]`, `[1,0]`,
  `[0,1]`, with quadrances `(2,1,1)` and spreads `(1,2,2)`.
- The non-null part of Exercise 10.11 is `FieldFive.exercise_10_11_nonNull`:
  every triangle over the executable five-element field is isosceles and any
  two have spread multiset `{3,3,1}`.  The corrected null part is
  `FieldFive.exercise_10_11_singlyNull`.  An exactly-one-null-side triangle
  can be relabelled by one of three explicit permutations, and its sole
  defined spread is `1` or `3`; both values have literal witnesses in
  `ExerciseTenEleven.exercise_10_11_null_examples`.  The same examples exhibit
  a noncollinear two-null-side triangle, for which no vertex meets the book's
  two-non-null-lines premise for defining a spread, so the printed blanket
  similarity claim does not apply in its own stated language.
- Exercise 10.12 is `ExerciseTenTwelve.exercise_10_12`.  Exact finite
  Gaussian-rational arithmetic factors the Triple-spread polynomial into its
  two displayed linear factors and proves that the denominator-free Spread
  laws force exactly two quadrance pairs.  `input_values`,
  `third_spread_values`, and `quadrance_values` expose all results in ordinary
  fraction notation.  The source's second pair has both real-part signs
  reversed: `printed_second_pair_counterexample` refutes it, while
  `displayed_solutions` certifies the corrected pair
  `(-10872+2232i)/11881`, `(-7929-7578i)/11881`.
- All numbered theorems, Example 10.1, and Exercises 10.1–10.12 in Chapter 10
  are formalized, subject to the explicit corrections for Exercises 10.6,
  10.11, and 10.12 above.

### Chapter 11

- Theorem 72 is `triangle_proportions`, proving the printed chain
  `r₁/r₂ = s₁R₁/(s₂R₂) = Q₁R₁/(Q₂R₂)`.  Its stronger denominator-free core
  is `triangle_proportions_cleared`; `triangle_proportions_of_spread_laws`
  follows the book's proof verbatim from the three displayed Spread-law
  quotient equalities, with every cancellation certificate explicit.
- Theorem 73 is `quadrilateral_proportions`, with the denominator-free core
  `quadrilateral_proportions_cleared` and the book-proof interface
  `quadrilateral_proportions_of_spread_laws`.
- Theorem 74 is `two_struts`.  `quadTriple_scale` proves the required
  homogeneity, while `two_struts_of_proportions` begins with the two collinear
  quad triples and the two proportions produced in the geometric proof, then
  normalizes them constructively to `{r,rp,mp}` and `{p,rp,nr}`.
- Theorem 75 is `stewart`.  A direct finite dot/determinant identity proves the
  displayed formula from the incidence certificate that `D` lies on `A₁A₂`;
  this single polynomial proof covers both `R₃ ≠ 0` and `R₃ = 0` without the
  source's case split, division, or an unnecessary non-null premise.
- Theorem 76 is `median_quadrance`; it removes the printed but unnecessary
  `Q₁ ≠ 0` premise and exposes only `2 ≠ 0`.  Exercise 11.7 is
  `exercise_11_7`, with `exercise_11_7_cleared` as its denominator-free form.
- Theorem 77 is `median_spreads`.  Its three printed values share the explicit
  denominator `2(s₂+s₃)-s₁`; `median_spreads_cleared` proves all three product
  identities before any division.
- Theorem 78 is `menelaus`.  `menelaus_cleared` retains the common product
  `r₁r₂r₃`, and `menelaus_of_spread_laws` obtains the three cyclic
  cross-products from exactly the quotient equalities printed in the proof.
- Theorem 79 is `alternate_spreads`; its retained-factor form is
  `alternate_spreads_cleared`, and `alternate_spreads_of_spread_laws` consumes
  the three cyclic quotient equalities from the book.
- Theorem 80 is `ceva`.  `ceva_cleared` retains the common spread product,
  while `ceva_of_triangle_proportions` combines the three displayed
  Triangle-proportion ratios with Alternate spreads exactly as in the source.
- Exercise 11.1 is `exercise_11_1`.  `spreadTriple_one_iff` supplies
  `s₁+s₂=1`; the Triangle-proportion cross-product then proves the reciprocal
  formula, with `exercise_11_1_cleared` retaining its single common
  denominator.
- Example 11.1 is `ChapterElevenExamples.ExampleElevenOne.example_11_1`.
  Scaling the two Two-struts quad triples by `256` gives exactly the printed
  factors `(64m-9)(64m-81)` and `(36n-25)(36n-121)`, without selecting roots.
  Exercise 11.2 is `exercise_11_2`, proving the common equation
  `(x-r-1)²=4r`; Exercise 11.3 is `exercise_11_3`, with the stronger cleared
  conclusion `4p=1` in `exercise_11_3_cleared`.
- Exercise 11.4 is corrected by `exercise_11_4_corrected`.  After the two
  bisector ratios normalize the Two-struts triples, their exact equations are
  `(ms₂+s₁+s₃)²=2((ms₂)²+s₁²+s₃²)` and its cyclic `n` counterpart.  The PDF
  omits the `(ms₂)²` and `(ns₁)²` terms.  The equilateral-spread specialization
  `ExerciseElevenFour.printed_equations_counterexample` refutes both printed
  equations while `corrected_equations` certifies the repaired ones.
- Exercise 11.5 is `exercise_11_5`.  Stewart's identity handles unequal base
  parts by finite cancellation; equal parts force the displayed point to be
  the midpoint, where the cleared median identity completes the same product
  formula.  Exercise 11.6 is `exercise_11_6`, with
  `exercise_11_6_geometric` deriving its two alternatives directly for an
  equilateral triangle and a point on its non-null base.
- Exercise 11.8 is `ExerciseElevenEight.exercise_11_8`: the three side
  midpoints satisfy the quadrance-product relation but have nonzero point
  determinant.  Exercise 11.10 is `ExerciseElevenTen.exercise_11_10`: the
  literal side points have quadrance pairs `(8,32)`, `(9,9)`, `(144,36)`, so
  the products agree, while the three cevian lines have nonzero line
  determinant and hence no common point.
- Exercise 11.9 is `exercise_11_9_quadrilateral`.  Its requested general
  `n`-gon form is `exercise_11_9_polygon`, stated for four displayed finite
  scalar lists: entrywise Spread-law cross-products telescope after the
  caller supplies the explicit cyclic quadrance rotation and its nonzero
  finite product.
- Exercise 11.11 is answered by `exercise_11_11_menelaus_relaxed` and
  `exercise_11_11_ceva_relaxed`: null data preserve exact product identities
  with the formerly cancelled spread factor still visible.
  `ExerciseElevenEleven.null_factor_counterexample` shows constructively that
  this retained-factor equation need not imply the ordinary quadrance-product
  conclusion when the common factor vanishes.
- All numbered theorems, Example 11.1, and Exercises 11.1–11.11 in Chapter 11
  are formalized, subject to the explicit Exercise 11.4 correction above.

### Chapter 12

- Theorem 81 is `circumcenter`.  `circumcenterPoint` is the executable
  intersection of two displayed perpendicular bisectors; noncollinearity
  proves that intersection denominator nonzero, and equal-quadrance
  transitivity proves incidence with the third bisector.  `circumquadrance`
  records the resulting common quadrance.
- Theorem 82 is `extended_spread_law`.  The stronger polynomial lemma
  `circumquadrea_identity` proves `𝒜K = Q₁Q₂Q₃` for any displayed common-
  quadrance center; Quadrea spread and the ordinary Spread law then give the
  book's complete quotient chain.  `extended_spread_law_cross_products`
  recovers the three division-free identities `sᵢ(4K) = Qᵢ`.
- Exercise 12.1 is `exercise_12_1`, a universal finite chord theorem.
  For a displayed equal-radius center and chord midpoint it derives the two
  equal center spreads from the right-triangle Spread ratio and the cleared
  Extended-spread identity, then derives the endpoint complement by
  Complementary spreads.  Instantiating it with the chords `A₂A₃` and
  `A₁A₃` gives all three printed assertions without the source proof's
  generic-position choice.
- Exercises 12.2 and 12.3 are `exercise_12_2` and `exercise_12_3`, each paired
  with a denominator-free `_cleared` theorem.
- Theorem 83 is `circumcenter_formula`.  `antisymmetricTripleProduct` encodes
  the source's six-term bracket notation, and `circumcenterFormula` is the
  exact printed coordinate pair.  The proof identifies it with the executable
  perpendicular-bisector intersection from Theorem 81.
- Theorem 84 is `affine_circumcenter`.  `affineCircumcenterPoint` uses exactly
  the three printed cyclic weights, while `affine_circumcenter_weights_sum`
  verifies independently that they sum to one.
- Theorem 85 is `orthocenter`.  `orthocenterPoint` is the executable
  intersection of two altitude lines, and the identically zero determinant of
  all three altitude equations proves concurrence.  The result strengthens the
  source by requiring only noncollinearity, not non-null sides.
- Theorem 86 is `orthocenter_formula`.  `orthocenterFormula` encodes the two
  printed antisymmetric numerators and is proved equal to the executable
  altitude intersection from Theorem 85.
- Theorem 87 is `affine_orthocenter`.  `affineOrthocenterPoint` uses the three
  printed cyclic beta weights, and `affine_orthocenter_weights_sum` proves
  their affine normalization.
- Theorem 88 is `incenter`, stated for the three displayed non-null side lines.
  Reflection proves the first two chosen bisectors nonparallel; their explicit
  intersection has equal quadrance to all three sides, and a constructed
  square witness selects a third bisector through that point.
- Theorem 89 is `incenter_spread`, in the translated-origin coordinates used
  by the source's computer proof.  `normalizedIncenterThirdLine` joins that
  origin to the two reflected sides' intersection, and
  `normalized_incenter_third_spread_eq_cross` is the cleared polynomial
  computation from which the printed complement follows by Fibonacci.
- Exercise 12.6 is `exercise_12_6`, with its first displayed equality recorded
  separately as `exercise_12_6_identity`.
- Theorem 90 is `inquadrance`, with `inquadrance_cleared` retaining the final
  factor `1-u₃` before cancellation.  `incenter_common_inquadrance` separately
  proves equality of the three point-to-side quadrances from the two chosen
  bisectors.
- Exercise 12.4 is `exercise_12_4_first` and `exercise_12_4_second`.
  `equal_quadrance_center_collinear_of_null` proves directly that a point
  equidistant from the ends of a null segment lies on its line; applying it
  to two independent null sides forces the circumcenter to their common
  vertex without selecting a null direction or square root.
- Exercise 12.5's displayed factorization is `exercise_12_5_identity`.
  `exercise_12_5_right_iff_sum_eq_eight_circumquadrance` combines it with the
  denominator-free circumquadrea identity and cancels only the explicitly
  nonzero quadrea, giving all three possible right-vertex equations.
- Exercise 12.7 is `exercise_12_7`.  The reusable finite root calculation
  `alternate_spread_root_sum` selects the other branch of the common
  Triple-spread quadratic, after which the source's quotient follows from
  `u₁≠1/2` with the `2≠0` premise exposed.
- Exercise 12.8 is `exercise_12_8`.  It combines the four explicitly selected
  bisector-branch inquadrance formulas, three double-spread identities, and
  Exercise 12.2's area formula in one finite polynomial calculation.
- Example 12.1 is the closed `F₁₃` certificate in
  `ChapterTwelveExamples.ExampleTwelveOne`.  It checks the four printed
  points, noncollinearity, all six non-null lines, spreads `6,7,4`, the three
  displayed Spread triples, the literal line representatives, and `r₁=8`
  together with Exercise 12.7's quotient.
- Example 12.2 is the exact Gaussian-rational certificate in
  `ChapterTwelveExamples.ExampleTwelveTwo`.  It checks the corrected literal
  coordinates, noncollinearity, all three displayed spreads, quadrea and
  circumquadrance, the six `hᵢ`/`jᵢ` bisectors, all six printed line
  intersections for the three other incenters, and all four common
  inquadrances.  `displayed_inquadrance_formula_checks` verifies both the
  Inquadrance theorem and Exercise 12.8's product on those literal values.
- All numbered Chapter 12 theorems, examples, and exercises are formalized.

### Chapter 13

- `PlaneIsometry` is the constructive form of the definition in §13.1: it
  stores an executable point map, its executable inverse, both cancellation
  laws, and the finite quadrance-preservation equation.  Exercise 13.1 is
  `PlaneIsometry.inverse` and `PlaneIsometry.comp`.
- Exercise 13.2 is realized by `rotationInPointIsometry` and
  `lineReflectionIsometry`; `reflectPoint_preserves_quadrance` supplies the
  previously missing polynomial metric calculation for line reflection.
- Exercise 13.3 is completed in both directions by
  `centralLine_reflection_is_central` and
  `centralReflection_has_unique_mirror`.  The latter constructs an executable
  mirror and proves uniqueness using `Line.Equivalent`, the project’s
  quotient-free equality of ordered line proportions.
- Examples 13.1–13.3 are the executable isometries `translation`,
  `centralReflection`, and `centralRotation`, including their displayed
  inverse formulas and proofs that the two central maps fix the origin.
- Exercise 13.4 is `centralRotationPoint_ne_centralReflectionPoint`, with the
  necessary `2 ≠ 0` hypothesis exposed, and `identity_centralRotationPoint`
  identifies the identity as a central rotation.
- Exercise 13.5 is `exercise_13_5`; its component lemmas prove both printed
  composition formulas and that the resulting parameter pairs remain unit.
- Theorem 91 is `PlaneIsometry.preservesCollinearity`.  It follows the printed
  proof through `PlaneIsometry.preservesQuadrea` and the Triple-quad formula;
  characteristic two is explicitly excluded because the book's quadrance
  degenerates there and cannot detect collinearity.
- Theorem 92 is `PlaneIsometry.specifiedByReferencePoints`.  The supporting
  theorem `PlaneIsometry.fixingReferencePoints_eq_identity` subtracts the
  three preserved-quadrance equations to recover both point coordinates, and
  the main proof applies it to the displayed inverse-composite isometry.
- Theorem 93 is `PlaneIsometry.orthogonalityClassification`.  The finite lemma
  `perpendicularUnitPair_orientations` selects one of the two possible second
  unit vectors by decidable equality, after which Theorem 92 identifies the
  entire map as the corresponding central rotation or reflection.
- Theorem 94 is `PlaneIsometry.isometryClassification`.  Its canonical
  executable factors are `PlaneIsometry.translationComponent` and
  `PlaneIsometry.orthogonalityComponent`; the theorem includes pointwise
  existence and uniqueness of both factors.
- Exercise 13.6 is `rotationInOrigin_eq_centralRotationPoint` together with
  `rotationInPoint_decomposition`.  Exercise 13.7 is
  `lineReflection_decomposition`, with `centralLine_reflection_formula`
  recording the printed central-reflection coordinates.
- All numbered theorems, examples, and exercises in Chapter 13 are formalized.

### Chapter 14

- `RegularThreeStar` is the finite order-three instance of the source's regular
  star definition: it stores three non-null, mutually nonparallel lines and
  the three cyclic reflection-lineation equations.  Its adjacent-spread
  equalities are derived rather than included as assumptions.
- Theorem 95 is `order_three_star`.  The forward proof follows the source
  through Three equal spreads and the displayed spread-number square witness;
  the converse `orderThreeStar` constructs exactly the three printed lines.
  The necessary characteristic-two exclusion is explicit.
- Example 14.2 is `example_14_2_fieldEleven`, using the printed root `5` in
  `F₁₁`.
- Example 14.1 is the finite Euler obstruction
  `ChapterFourteenExamples.not_nonzeroSquare_of_frobenius_neg`, specialized
  by `ExampleFourteenOne.field_three`, `.field_five`, `.field_seven`,
  `.field_seventeen`, and `.field_nineteen`.  Each exclusion uses only the
  displayed characteristic equation and pointwise finite Frobenius law; no
  carrier enumeration or global finite-field hierarchy is imported.
- Example 14.3 is the closed `F₁₃` certificate
  `ExampleFourteenThree.example_14_3`.  It constructs the order-three star
  from `4²=3` and checks the three printed slopes `0`, `4`, and `9`.
  Example 14.4 is `ExampleFourteenFour.example_14_4`; the project-owned
  constructive reduced-fraction square theorem excludes a rational square
  root of three and hence any rational order-three star.
- `RegularFiveStar` is the completely finite order-five star data: five
  non-null lines, all ten nonparallel pairs, and the five cyclic reflection
  equations.  Theorem 96 is `order_five_star`.  Its forward proof obtains the
  printed conditions `r² = 5` and `2(5-r) = v²` from `S₅(s) = 0`; its converse
  `orderFiveStar` verifies the five coefficient triples printed in the book.
  All cancellations and polynomial identities are explicit, including the
  characteristic-two exclusion.
- Example 14.5 is `ExampleFourteenFive.field_three` through
  `.field_seventeen`.  The common complete-square lemma
  `nonzero_spreadPolynomial_five_root_gives_square_five` shows that every
  nonzero root of `S₅` supplies a nonzero square root of five; the five
  characteristic clauses then give their literal finite Euler obstructions,
  with characteristic five handled directly as `S₅(s)=s⁵`.
- Example 14.6 is `ExampleFourteenSix.root_classification` and
  `.nonzero_roots_not_spread`: in characteristic eleven the only `S₅`
  roots are `0`, `7`, and `8`, while the two nonzero values fail the exact
  spread-number square test.  Example 14.7 is the executable `F₁₉` star
  `ExampleFourteenSeven.star`; `example_14_7_lines` checks its five printed
  slopes and `example_14_7_values` certifies both printed nonzero roots and
  their spread witnesses.
- `RegularSevenStar` represents precisely the seven requested reflection
  iterates, with pairwise nonparallelism bounded by `Fin 7` and two finite
  wraparound equations.  Theorem 97 is `order_seven_star`.  The forward proof
  factors `S₇(s)` as printed.  The converse `orderSevenStar` constructs the
  initial lines `⟨0:1:0⟩`, `⟨s:v:0⟩`, performs only the required finite
  reflections, and uses five explicit Bézout identities to rule out every
  shorter period.
- Example 14.8 is `ExampleFourteenEight.field_three` through
  `.field_twentyThree`, together with `.field_thirteen_roots` and
  `.field_thirteen_roots_not_spread`.  Six literal integer-polynomial Bézout
  certificates are checked by the primitive-recursive
  `RFAP.IntegerPolynomialCertificate`; characteristic seven reduces directly
  to `-s³`.  In characteristic thirteen the exact roots are `2`, `5`, and
  `11`, and three finite Euler certificates show that none is a spread
  number.  No field carrier or root set is enumerated.
- Example 14.9 is `ExampleFourteenNine.roots`, `.values_are_spread`, `.star`,
  and `.lines`.  Over any explicitly supplied characteristic-twenty-nine
  field, the cubic roots are exactly `6`, `7`, and `25`; the square witnesses
  `12`, `4`, and `3` certify their spread status.  The finite Theorem 97
  constructor gives a regular star, and five explicit reflection steps
  normalize its seven lines to the printed slopes
  `0,15,11,20,9,18,14`.
- Example 14.10 is `ExampleFourteenTen.cubic_has_no_rational_root` and
  `.no_rational_star`.  The computable reduced numerator and denominator give
  the complete finite Eisenstein-at-seven argument, rather than a completed
  real-root theorem.  `first_rational_bracket`, `second_rational_bracket`, and
  `third_rational_bracket` retain the three printed decimal approximations as
  exact millionth-width rational intervals with opposite cubic signs.
- `FiniteRegularStar` stores only the requested finite reflection prefix and
  its two closing representatives.  `exercise_14_1` proves the source's
  shifted product identity for every three requested natural indices, and
  `regularPolygonVertexAt_succ` uses it to identify the closed formula
  `A₂ₖ=σ_{lₖ}(A₀)` with the successive construction through `l₂ₖ₊₁`.
  Every computed vertex lies on `l₂ₖ`, has the common radial quadrance, and
  the finite closing representative returns `A₂ₙ` to `A₀`.
- Example 14.11 is `ExampleFourteenEleven.example_14_11`.  Doubling modulo
  five is represented by the literal permutation `[0,2,4,1,3]`; its explicit
  inverse proves the five radial lines, and hence the five vertices
  `A₀,A₂,A₄,A₆,A₈`, pairwise distinct.
- Example 14.12 is `ExampleFourteenTwelve.example_14_12`.  The three repeated
  radial-line pairs are separated using
  `hexagon_opposite_lines_perpendicular`: the finite cyclic-reflection and
  closure equations force `lₖ ⟂ lₖ₊₃`.  Composition of those two point
  reflections is proved directly to be rotation in the center, so a repeated
  vertex would contradict the supplied noncentral initial point.  Thus all
  six displayed vertices through `A₁₀` are distinct.
- `PolygonTriangleConfiguration` is the finite three-vertex window needed by
  the polygon construction.  Theorem 98 is `polygon_triangle`, with all three
  quadrance and all three spread conclusions printed in the source.  The new
  geometric lemma `reflectPoint_chord_quadrance_eq_spread` proves the
  Isosceles-reflection step directly from point-to-line quadrance; the rest of
  the proof uses the ordinary Spread law, Equal spreads, and explicit finite
  cancellation.
- Exercise 14.2 is `exercise_14_2`.  It states the source's general
  `Q(A₀,A₂ₖ)=4Sₖ(s)Q` formula for a requested finite `k`, consuming the
  finitely computed spread of `l₀,lₖ` rather than a completed polygon
  sequence.
- Exercise 14.3 is split at the constructive boundary into exact algebra,
  finite decimal evidence, and finite geometry.  For an explicitly supplied
  nonzero root `r²=5`,
  `ExercisesFourteenThreeFour.nontrivial_zeroes` proves that
  `α=(5-r)/8` and `β=(5+r)/8` are exactly all nonzero roots of `S₅`;
  the proof factors a finite difference of squares and selects no algebraic
  closure.  `Figure.exercise_14_3` derives all six printed quadrance formulas
  for `P,A,M,B,F,E` from Theorem 98 and the two midpoint identities.
  `Decimal.alphaBracket` and `.betaBracket` certify the printed
  approximations by exact millionth rational intervals with opposite
  quadratic signs, without completed decimals or real limits.
- Exercise 14.4 is `ExercisesFourteenThreeFour.Figure.exercise_14_4`.
  The logistic identities `β=4α(1-α)` and `α=4β(1-β)` identify
  the two radial spreads, and finite cancellation proves that `β:α` is
  both their spread proportion and `Q(B,E):Q(A,B)`.
- Exercise 14.5 is the fully executable `F₁₉` certificate
  `ExerciseFourteenFive.exercise_14_5`.  The two pentagons named by the
  source are actual `ConstructedRegularPolygon`s.  `diagonalStep` checks all
  five intersections at each of eighteen steps; the corresponding endpoint
  and nonparallel theorems certify every line and denominator.  The explicit
  nineteenth row is the source pentagon under the cyclic relabelling
  `i ↦ i+2`, proved by `recoveredAfterEighteen`.  This bounded orbit is not
  a global enumeration of the field carrier.
- All numbered theorems, examples, and exercises in Chapter 14 are now
  formalized at the stated finite constructive boundary.

### Chapter 15

- A conic is the finite coefficient record `Conic`; `Conic.evaluate` and
  `Conic.Contains` are its displayed polynomial and incidence equation.
  `Conic.RotationInvariant` is the source definition of center symmetry, while
  `Conic.isCenter_iff_rotationInvariant` proves it equivalent to the two
  displayed linear equations by using only two concrete test points in the
  reverse direction.
- Theorem 99 is `Conic.conic_center`.  In the nonsingular case,
  `Conic.centerPoint` is the exact printed formula and
  `Conic.center_eq_centerPoint` proves it is the unique center.  In the
  singular case, `Conic.CenterRowsEquivalent` is the quotient-free proportion
  `e:2f:b = 2d:e:a`; compatibility constructs a center explicitly and
  `Conic.secondCenter_of_discriminant_zero` supplies a nonzero kernel
  displacement to a distinct second center.  Incompatibility proves that no
  center exists.
- Example 15.1 is `Conic.example_15_1`, together with the original
  rotation-invariance statement `Conic.example_15_1_rotationInvariant`.
- Example 15.2 is
  `ChapterFifteenCentralCircles.ExampleFifteenTwo.example_15_2`.  It checks
  Figure 15.1's literal eleven-by-eleven central-quadrance matrix over the
  executable `F₁₁` model, proves its 121 displayed positions
  duplicate-free, and verifies the printed one-point null-circle count and
  twelve-point count for each of the ten non-null labels.  Exercise 15.3 is
  `ChapterFifteenCentralCircles.ExerciseFifteenThree.exercise_15_3`, with the
  corresponding thirteen-by-thirteen `F₁₃` matrix, 169 distinct
  displayed positions, twenty-five null-circle points, and twelve points for
  each non-null label.  The generic
  `ChapterFifteenCentralCircles.displayedCirclePoint_contains` connects every
  filtered entry to the actual normalized circle conic, while
  `circleConic_origin_isCentral` verifies that each such conic is central.
  As elsewhere, the coordinate lists certify the literal finite figures and
  do not claim to globally enumerate an ambient field carrier.
- Exercise 15.1 is `Conic.exercise_15_1_first` and
  `Conic.exercise_15_1_second`: the first conic has exactly the centers
  `[u,-u]`, and the second has none.  Exercise 15.2 is `Conic.exercise_15_2`;
  every point on the line through two distinct centers is a center, proved via
  the finite affine decomposition from Theorem 9.
- `Conic.IsCirclePresentation` encodes `Q(X,C)=K` while retaining an arbitrary
  nonzero common coefficient scale.  `Conic.contains_iff_quadrance_eq` proves
  that its incidence equation is exactly the displayed quadrance equation.
- Theorem 100 is `Conic.circle_uniqueness`, with the unique-existence packaging
  `Conic.circle_has_unique_presentation`.  It recovers both center coordinates
  and the quadrance by explicit finite cancellation, under the visible
  characteristic-two exclusion.
- Exercise 15.4 is `Conic.exercise_15_4`.  Its reverse direction explicitly
  constructs the center and quadrance from `e=0` and `d=f≠0`.  Exercise 15.5 is
  `Conic.exercise_15_5`, proved in the requested generalized form: over any
  constructive field of characteristic thirteen, the central null circle is
  exactly the union of the lines `⟨2:3:0⟩` and `⟨3:2:0⟩`.  The proof uses their
  direct finite polynomial factorization, not an enumeration of field points.
- Exercise 15.6 is `Ribbon.exercise_15_6`.  `Ribbon.PresentationData` retains
  the non-null line, ribbon quadrance, and explicit nonzero coefficient scale
  for the cleared equation `(ax+by+c)²=K(a²+b²)`.  The stronger theorem
  `Ribbon.PresentationData.isCenter_iff_contains` identifies the entire center
  locus with the defining line.  Equality of those finite incidence loci
  proves the two lines equivalent, after which their explicit coefficient
  scale and the nonzero line norm recover the quadrance uniquely.
- `Conic.ParabolaPresentationData` records the non-null directrix, the focus-off-
  directrix certificate, and the six scaled coefficients obtained by clearing
  the denominator in `Q(X,F)=Q(X,l)`.  `Conic.parabolaConic_evaluate` is the
  direct polynomial expansion, while
  `Conic.parabolaConic_contains_iff_equal_quadrances` recovers the source's
  quotient equation with every cancellation certificate visible.
- Theorem 101 is `Conic.parabola_uniqueness`, with the unique-existence package
  `Conic.parabola_has_unique_focus_directrix`.  The proof implements both
  finite coordinate charts: when the directrix's first coefficient is nonzero
  it recovers the normalized slope, intercept, and focus; when it is zero it
  recovers the complementary normalization by a sum/difference factorization.
  Directrices are unique under the quotient-free relation `Line.Equivalent`.
- Example 15.3 is `Conic.example_15_3` and
  `Conic.example_15_3_equation`, including the exact conic
  `⟨0:0:1:-4a:0:0⟩`.  Example 15.4 is its executable `F₁₁` instance
  `Conic.example_15_4` and `Conic.example_15_4_equation`.
  Exercise 15.7 is `Conic.exercise_15_7`: combining the two equations of a
  hypothetical center forces the focus onto the directrix, contradicting the
  finite presentation certificate.
- Exercise 15.8 is `Conic.exercise_15_8`.  The executable
  `Conic.parabolaAxis` is the altitude from the focus to the directrix;
  `Conic.parabolaAxis_isAxis` proves that its reflection preserves the exact
  displayed conic equation.  For an arbitrary proposed axis,
  `Conic.reflectedPresentation_of_axis` constructs the reflected focus and
  directrix as a second valid presentation.  Six explicit polynomial probes
  recover its coefficients, Theorem 101 fixes the reflected focus/directrix,
  and the finite reflected-line calculation proves the mirror equivalent to
  the canonical altitude.  Thus uniqueness does not select an eigenvector or
  a root.
- Exercise 15.9 is `Conic.exercise_15_9`.  `Conic.parabolaVertex` is the
  midpoint of the focus and its altitude foot on the directrix.  It is proved
  incident with both the parabola and its axis.  Any other common point has
  the same directrix foot and equal quadrances to the focus and that foot, so
  finite non-null-side midpoint uniqueness identifies it with the displayed
  vertex.
- `Quadrola.Presentation` records the four nondegeneracy clauses of §15.4.
  `Quadrola.conic` is the executable six-coefficient expansion of its
  Archimedes equation, and `Quadrola.conic_evaluate` proves Exercise 15.11's
  quartic cancellation exactly.  Example 15.5 is
  `Quadrola.example_15_5_focus_quadrance`,
  `Quadrola.example_15_5_equation`, and
  `Quadrola.example_15_5_alternate_foci`, with
  `Quadrola.example_15_5_alternate_presentation` verifying all four
  nondegeneracy clauses: an explicit square root of `-1` produces the second
  displayed focal pair and associated quadrance.  Example 15.6 is the closed executable `F₁₁`
  certificate `ChapterFifteenExamples.ExampleFifteenSix.example_15_6`; its
  constructed six coefficients are proved to be three times the printed
  representative `⟨7:0:5:0:0:1⟩`, without enumerating the field.
- Exercise 15.10 is `Quadrola.exercise_15_10`.  The proposition
  `Quadrola.NoSquareRootOfNegativeOne` states the book's finite field
  hypothesis directly, while `Quadrola.CoefficientScale` is an explicit
  quotient-free witness that two six-coefficient equations represent the
  same conic proportion.  The proof first recovers their common focal
  midpoint as the unique center, then shows that the coefficient scale must
  be one.  The normalized quadratic coefficients determine the associated
  quadrance and focal-difference vector up to sign, so the two foci agree as
  an unordered pair.  No roots, carrier enumeration, or choice are used.
- Exercise 15.12 is `Quadrola.exercise_15_12`: the midpoint of the two foci
  satisfies both center equations.  `Conic.IsAxis` retains the source's
  finite equation-preservation definition.  Exercise 15.13 is
  `Quadrola.exercise_15_13`; reflection in the non-null focal line fixes both
  foci, reflection in their non-null perpendicular bisector exchanges them,
  and these two inequivalent mirrors preserve the Archimedes equation.
- `Grammola.Presentation` records the two non-null, nonparallel,
  nonperpendicular diagonal lines and nonzero associated quadrance from
  §15.5.  `Grammola.conic` clears exactly the two line norms,
  `Grammola.conic_contains_iff` recovers the metric locus, and Exercise 15.15
  is `Grammola.exercise_15_15`: the explicit intersection of the two
  diagonals satisfies both center equations.
- Exercise 15.14 is `Grammola.exercise_15_14`.  The conic-determined binary
  quadratic `Grammola.diagonalRecoveryValue` factors as a certified nonzero
  scalar times the product of the two diagonal direction forms.  Its two
  linear factors therefore recover the diagonal directions up to swapping;
  the unique center recovers their affine offsets.  Evaluating the conic at
  that center and comparing its nonzero quadratic trace recovers the
  associated quadrance.  The proof selects no roots and diagonalizes no
  matrix.
- Example 15.7 is `Grammola.example_15_7_equation` and
  `Grammola.example_15_7_presentation`.  The latter records two necessary
  source corrections: besides `a² ≠ 1`, one needs `a ≠ 0` to keep the
  displayed diagonals distinct and `a²+1 ≠ 0` to keep them non-null over a
  general field.  Example 15.8 is the exact constructive-rational theorem
  `ChapterFifteenExamples.ExampleFifteenEight.example_15_8`, including the
  normalized diagonal representatives and the four conditional square-root-
  of-five points.  Example 15.9 is the closed `F₁₁` certificate
  `ChapterFifteenExamples.ExampleFifteenNine.example_15_9`, with all four
  displayed point incidences and the metric-locus equivalence checked
  independently.
- Exercise 15.16 is false as printed.
  `ChapterFifteenExamples.ExerciseFifteenSixteen.exercise_15_16_printed_counterexample`
  gives the claimed grammola an explicit valid quadrola presentation in
  `F₁₁`: foci `[0,4]` and `[0,7]`, associated quadrance `8`, and coefficient
  scale `5` recover exactly `2x²+8y²-5=0`.  The separate theorem `same_locus`
  verifies the metric quadrola and printed grammola equations pointwise,
  without enumerating the field.
- Exercise 15.17 is
  `ChapterFifteenExamples.ExerciseFifteenSeventeen.exercise_15_17`.  Over any
  constructive field with `2≠0`, the foci `[1,0]`, `[-1,0]` and associated
  quadrance `2` give a valid quadrola whose quadratic trace `d+f` is zero.
  `Grammola.conic_trace_nonzero` proves every valid grammola has trace
  `2‖l₁‖‖l₂‖≠0`; consequently no nonzero coefficient scale can identify the
  example with a grammola, in either direction.
- Exercise 15.18 is `Grammola.exercise_15_18` in the stronger exact form.
  `Grammola.HasExactlyTwoAxes` stores two inequivalent equation-preserving
  mirrors and requires every other axis to be equivalent to one of them.  An
  explicit square witness for the product of the diagonal norms constructs
  the positive and negative normalized vertex bisectors; direct reflected
  line-value identities prove both are axes.  Conversely, the unique center
  lies on every axis, and two finite probes force the axis's mixed quadratic
  term to vanish.  The resulting factorization proves
  `Grammola.axis_isVertexBisector`, so Theorem 45 supplies both the square
  witness and the exhaustive two-axis classification.  No square root is
  selected: the witness is consumed as data.
- `Conic.IntersectsAt`, `Conic.IsChord`, and
  `Conic.HasThreeDistinctIntersections` give the finite witness forms of the
  definitions in §15.6.  Theorem 102 is `Conic.conic_line_intersection`.
  `Conic.evaluate_thalesPoint` proves the exact quadratic interpolation
  identity on a line; a third distinct zero supplies an explicit nonzero
  scalar factor, so the restriction's quadratic coefficient cancels and every
  requested point on the line is proved incident with the conic.
- All numbered theorems, examples, and exercises in Chapter 15 are now
  formalized, subject to the explicitly recorded source corrections.

### Chapter 16

- `Conic.IsDiameter` and `Conic.IsCircumcircleOf` give finite witness forms of
  the opening definitions.  Theorem 103 is `Conic.right_diameter`, with its
  metric core separated as `Conic.right_diameter_of_center_eq_midpoint`.
  The printed proof uses uniqueness of a midpoint on an equidistant line; over
  the book's general fields that step requires the diameter side to be
  non-null.  The Lean theorem exposes this omitted premise and is therefore
  marked corrected.
- Exercise 16.1 is `Conic.exercise_16_1`.  From the one intersection stored by
  a diameter it explicitly constructs the antipodal point by rotation in the
  center, proves it lies on both the line and circle, and uses the nonzero
  circle quadrance to prove the two points distinct.
- Theorem 104 is `Conic.circle_chord`.  The constructive core
  `Conic.radius_eq_zero_of_equal_radii_and_null_separation` replaces the
  source's selected square root of `-1` by two denominator-free square
  identities: distinct equal-radius points with null separation force the
  common radius to vanish.
- Exercise 16.2 is `Conic.exercise_16_2`.  Each diameter yields an explicit
  nonzero square witness for `‖l‖K`; combining the two witnesses constructs a
  square root for `‖l₁‖‖l₂‖`, and Theorem 45 returns an actual vertex bisector.
  Exercise 16.3 is `Conic.exercise_16_3`: three intersections would make the
  circle's restriction to the line identically zero, contradicting its
  explicit nonzero quadratic coefficient.
- Theorem 105 is `Conic.subtended_spread`.  For three distinct points on a
  non-null circle it proves that the third point's spread is the fixed finite
  quotient `Q(A₁,A₂)/(4K)`, and that the central spread is its second spread
  polynomial `4s(1-s)`.  The proof combines the denominator-cleared Extended
  spread law with a direct two-radius determinant identity; it selects no
  roots and constructs no completed circle or infinite point family.
- Theorem 106 is `Conic.equal_products`.  Its stronger denominator-free core
  `Conic.chord_quadrance_product_eq_circle_power` proves that the product cut
  out on any displayed chord equals the square of the intersection point's
  circle-power.  Applying that identity to the two chords proves the printed
  equality without the source proof's spread divisions, non-null cases, or
  cancellation premises.
- Exercise 16.4 (Van Schooten) is `Conic.exercise_16_4`.  The reusable lemma
  `Conic.fourPointCircleDeterminant_eq_zero` supplies the exact finite
  concyclicity equation.  For the equilateral triangle, three direct
  two-dimensional determinant identities identify its square with the
  Archimedes polynomial of the three quadrances from the fourth point; the
  triangle's noncollinearity makes the sole final scale cancellable.
- Exercise 16.5 (Brahmagupta) is `Conic.exercise_16_5`.  The signed formula
  `Conic.thalesPoint_circle_power_of_circle` retains a finite parameter on
  each diagonal, so their common circle-power equates the two unsquared chord
  products.  Expanding the displayed midpoint and using perpendicularity of
  the diagonal direction vectors proves its incidence with the requested
  altitude, without an orientation or square-root choice.
- Exercise 16.6 is corrected by `Conic.exercise_16_6`, which exhibits the
  exact constant `2(Q(A,C)+K)`; `Conic.exercise_16_6_independent` gives the
  literal equality for any two requested circle points.  The printed exercise
  omits `K ≠ 0`: `Conic.exercise_16_6_null_circle_counterexample` evaluates a
  null circle and null diameter in `F₅` where the two sums differ.  Under the
  corrected premise, `Conic.diameter_nonNull_of_circleQuadrance_ne_zero` and
  midpoint uniqueness constructively force the equidistant points to be
  antipodal.
- Theorem 107 is `Conic.projective_circle`.  The finite definitions
  `Conic.projectiveCircle` and `Conic.projectiveCirclePoint` are respectively
  the equation `x²+y²-y=0` and the printed parameter pair
  `[λ/(1+λ²),1/(1+λ²)]`.  `Conic.projectiveCirclePoint_contains` clears the
  explicitly certified denominator, while
  `Conic.projectiveCirclePoint_exists` proves that a requested non-origin
  circle point has `y ≠ 0` and constructs `λ=x/y`.  The source's four
  displayed points are `Conic.projectiveCircle_four_points`, and
  `Conic.projectiveCircle_isCirclePresentation` verifies the stated center
  and quadrance.
- Exercise 16.7 is `Conic.exercise_16_7`.  The canonical ray
  `Conic.projectiveCircleLine λ = ⟨-1:λ:0⟩` contains both the origin and the
  corresponding parametrized point.  `Conic.projectiveCircle_origin_rays_equivalent_iff`
  proves injectivity of the point-to-ray map, while the second half of the
  exercise packages surjectivity onto every displayed origin line carrying a
  non-origin circle intersection.  Equality of line representatives remains
  the explicit `Line.Equivalent` relation; no quotient is introduced.
- Theorem 108 is `Conic.unit_circle`.  `Conic.projectiveToUnit` is the printed
  finite transform `[x,y] ↦ [2y-1,2x]`, and
  `Conic.projectiveToUnit_equation` proves that its unit-circle equation is
  exactly four times the projective-circle equation.  The reverse direction
  constructs `[y/2,(x+1)/2]` under the visible `2 ≠ 0` premise and invokes
  Theorem 107's witness recovery.  `Conic.unitCircle_four_points` verifies the
  four displayed points, while `Conic.unitCircle_isCirclePresentation`
  records the stated center and quadrance.
- Exercise 16.8 is `Conic.exercise_16_8`.  Finite Cartesian pairs carry the
  executable operations `Conic.gaussianMul` and `Conic.gaussianScale`, without
  introducing a completed complex carrier.  `Conic.unitCircleParameter` is
  the constructive inverse `y/(1+x)`, and
  `Conic.unitCirclePoint_existsUnique` proves the requested uniqueness.
  `Conic.imaginaryParameterPoint_is_intersection` proves the printed chord
  construction using two explicit displayed lines.  Finally,
  `Conic.rationalPolarPoint_mul` proves the polar multiplication law and
  `Conic.turnComposition_square_ne_negative_one` proves that the result stays
  in the chart.  The necessary exception `1-λ₁λ₂ ≠ 0` is visible: otherwise
  `Conic.gaussianMul_unitCirclePoint_eq_excluded` proves that the product is
  exactly the chart's excluded point `[-1,0]`.  The shared `turnComposition`
  definition formally records why Exercise 9.2's formula appears here.
- All numbered theorems and exercises in Chapter 16 are formalized.

### Chapter 17

- `Quadrilateral` is the finite record requested by the book's definition:
  four displayed pairwise-distinct points and explicit noncollinearity proofs
  for all four triples.  Its `IsCyclic` predicate carries a concrete conic,
  center, quadrance, circle presentation, and four incidence certificates.
- Theorem 109 is `Quadrilateral.cyclic_quadrilateral`.
  `Quadrilateral.coordinateCircleDeterminant` expands the printed determinant
  with rows `[xᵢ²+yᵢ²,xᵢ,yᵢ,1]` using the explicit three-by-three operation
  `Quadrilateral.determinantThree`; it invokes no matrix determinant or
  permutation enumeration.  The forward implication reuses the Chapter 16
  four-point identity.  Conversely, the determinant constructs the normalized
  circle at the first three points' finite circumcenter and cancels their
  nonzero collinearity determinant to prove incidence of the fourth point.
- Theorem 110 is `Quadrilateral.cyclic_quadrilateral_spreads`.  The finite
  record `Quadrilateral.CyclicSubtendedSpreads` stores the six scalars and the
  four triangle `SpreadTriple` certificates used by the printed proof; two
  direct applications of `two_spread_triples` give the side Quadruple-spread
  equation and both displayed diagonal quotients.  For actual circle data,
  `Quadrilateral.normalizedCyclicSubtendedSpreads` constructs those values as
  `Q(Aᵢ,Aⱼ)/(4K)`.  Its proof invokes the Subtended-spread theorem at each
  requested vertex and exposes `K ≠ 0`, which is necessary over finite fields
  where a null circle can have null chords.
- Theorem 111 is `Quadrilateral.quadrilateral_circumquadrance`; its printed
  coefficients are `circumquadranceCoefficientP`,
  `circumquadranceCoefficientQ`, and `circumquadranceCoefficientR`.  The
  denominator-free identity `circumquadrance_polynomial_scaled_spread` proves
  that after `Qᵢⱼ=4Krᵢⱼ` the requested quadratic equals `256K⁶` times the
  Quadruple-spread polynomial.  Thus the formal proof avoids the source's
  cancellation of that factor.  Exercise 17.1 is the direct factorization
  `Quadrilateral.exercise_17_1`.
- Example 17.1 is fully evaluated in
  `ChapterSeventeenExamples.ExampleSeventeenOne`: both explicit `F₁₁`
  quadrilaterals, their common side quadrances, circle quadrances `2` and `9`,
  coefficient values, displayed lines and incidences, vertex and subtended
  spreads, Theorem 110 formulas, and polygon quadreas `4` and `9` are checked
  by kernel computation.  No enumeration of all field elements or roots is
  used.
- Theorem 112 is strengthened by
  `Quadrilateral.cyclic_quadrilateral_quadrea`: the requested equation holds
  for every displayed cyclic quadrilateral, without the source's solvability
  or nonzero-product assumptions.  The direct identity
  `Quadrilateral.cyclicQuadrea_polynomial_identity` shows that the polynomial
  residual is `-64` times the square of the four-point circle determinant.
  This replaces the source's long diagonal and circumquadrance elimination.
  `Quadrilateral.cyclicQuadrea_roots_vieta` proves the stated average and
  product laws for two distinct roots.
- Example 17.2 is `ChapterSeventeenExamples.ExampleSeventeenOne.example_17_2`,
  checking `m=1`, `p=3`, roots `4,9`, their average, and their product in
  `F₁₁`.
- Theorem 113 is `Quadrilateral.cyclic_signed_area`.  Its printed unit-circle
  chart is the executable pair `Quadrilateral.orientedUnitCirclePoint`, and
  `orientedUnitCirclePoint_contains` proves incidence.  The proof clears the
  four certified chart denominators and evaluates the finite shoelace sum;
  the necessary `2 ≠ 0` normalization premise is explicit.  Exercise 17.2 is
  `Quadrilateral.exercise_17_2`, including cancellation of the repeated
  point's chart factor to recover the printed triangle formula.
- Example 17.3 is the exact constructive-rational calculation in
  `ChapterSeventeenExamples.ExampleSeventeenThree`: side quadrances,
  coefficients `p,q,r,m`, both factorizations, and the exact circumquadrance
  and quadrea roots.  The source's decimal square-root approximations are
  represented by their exact squared rational data rather than completed
  real numbers.
- Theorem 114 is `Quadrilateral.ptolemy`.  The book's definition of
  solvability is the explicit proposition
  `Quadrilateral.CyclicSubtendedSpreads.IsSolvable`, requiring precisely the
  two diagonal-formula denominators to be nonzero.  The universal polynomial
  identity `Quadrilateral.ptolemy_cleared_factorization` verifies the printed
  auxiliary `B` factor after clearing those denominators; the final theorem
  uses Theorem 110 and cancels only their supplied nonzero certificates.
- Example 17.4 is
  `ChapterSeventeenExamples.ExampleSeventeenOne.example_17_4`: it evaluates
  the products to `7,2,10` in `F₁₁`, checks their quad-triple relation,
  and verifies that both sides of the source's centered-square calculation
  equal one.
- Theorem 115 is `Quadrilateral.four_point_relation`.  The Euler function is
  the source's explicit three-by-three determinant, and
  `Quadrilateral.euler_coordinate_identity` proves its vanishing directly
  from four displayed pairs of coordinates.
- Exercises 17.3 and 17.4 are `Quadrilateral.exercise_17_3` and
  `Quadrilateral.exercise_17_4`; the latter uses the explicit finite
  four-by-four expansion `Quadrilateral.determinantFour` to verify the
  displayed five-by-five Cayley--Menger determinant without permutation
  enumeration.  Exercise 17.6 is `Quadrilateral.exercise_17_6`, applying the
  Four point relation at an explicit circumcenter to recover the quotient.
- Exercise 17.5 is false as printed: its left parenthesis lacks a factor `2`
  before `P₃` and an overall division by `2`.
  `Quadrilateral.fourPoint_quadratic_identity` proves the cleared corrected
  polynomial, `Quadrilateral.exercise_17_5` proves the corrected quotient,
  and `ChapterSeventeenExamples.ExampleSeventeenOne.exercise_17_5_printed_counterexample`
  refutes the printed equation by kernel computation in `F₁₁` while its
  Four point premise remains true.
- All numbered Chapter 17 theorems, examples, and exercises are formalized.

### Chapter 18

- Theorem 116 is `euler_line`.  The centroid is the executable pair
  `centroidPoint`, and `euler_center_weight_identity` proves the coefficient
  relation `2αᵢ+βᵢ=1` for the affine circumcenter and orthocenter.
  Consequently `euler_center_relation` proves the stronger displayed identity
  `G=(2/3)C+(1/3)O`; `euler_line` converts it to the finite three-point
  collinearity determinant.  The denominator-cleared theorem
  `euler_center_cleared_coordinates` proves `2C+O=A₁+A₂+A₃` without requiring
  characteristic three to be excluded.  The characteristic-two requirement
  for the circumcenter and every later division premise remain explicit.
- Exercise 18.1 is `exercise_18_1`.  The two identities
  `centroid_quadrance_difference_first_second` and
  `centroid_quadrance_difference_second_third` prove constructively that the
  centroid, circumcenter, and orthocenter coincide exactly when all three
  quadrances agree.
- Exercise 18.2 is `exercise_18_2_formula` and
  `exercise_18_2_center_on_euler_line`.  The first proves the book's displayed
  bracket formula for `N`; the second proves directly that this midpoint of
  `C` and `O` lies on their line.
- Theorem 117 is `nine_point_circle`.  It constructs `ninePointCircle`
  explicitly and proves incidence for the three side midpoints, three
  altitude feet, and three vertex--orthocenter midpoints.  Its hypotheses
  expose exactly the source's non-null sides and the finite factor `2 ≠ 0`.
  The reusable right-midpoint proof includes coincident foot/end-point cases
  and does not hide any classical case selection.
- Example 18.1 is the closed executable certificate in
  `ChapterEighteenExamples.ExampleEighteenOne`.  It checks all printed
  coordinates, line incidences, centers, midpoints, quadrance-zero circle
  incidences, and Euler-line incidences in the seventeen displayed residue
  classes.  `no_third_altitude_foot` proves that the null third side and its
  altitude are disjoint.  This module evaluates only the literal source data;
  it does not enumerate the carrier or install a globally audited field
  instance.
- Exercise 18.3 is `exercise_18_3`.  The perpendicular-diagonal hypothesis
  gives a right midpoint parallelogram, while
  `altitudeFoot_diameter_quadrance` places each of the four opposite-side feet
  on the same explicit `eightPointCircle`.
- All numbered Chapter 18 theorems, its example, and its exercises are
  formalized.

### Chapter 19

- Theorem 118 is `Conic.translate_of_conic`.  The executable coefficient
  record `Conic.translateConic` preserves the quadratic part, and
  `Conic.translateConic_evaluate` proves the source's polynomial identity
  exactly, so incidence is transported in both directions.
- Theorem 119 is `Conic.tangent_to_conic`.  `Conic.taylorConic` moves the
  base point to the origin; `Conic.taylorConic_linear_coefficients` recovers
  the two first-order coefficients; and translating that linear part back
  gives the printed `Conic.tangentLine` representative and its incidence.
- Theorem 120 is `Conic.tangent_to_circle`.  It constructs the point--center
  line, proves the circle point non-singular, proves the tangent non-null, and
  identifies it up to `Line.Equivalent` with the altitude from the point to
  the point--center line.  The necessary `2 ≠ 0` and nonzero circle-quadrance
  premises are explicit.
- Theorem 121 is `Conic.parabola_reflection`.  The proof works directly with
  the scaled focus/directrix certificate, derives point--focus distinctness
  and first-order non-singularity, and proves the two spread quotients equal
  by a denominator-cleared polynomial calculation.  The source's implicit
  non-nullness of `AF` is exposed because otherwise `s(k,AF)` is undefined.
- All 121 numbered theorems in the source index are now formalized.
- Examples 19.1--19.3 are the exact translation, Taylor-conic, and tangent
  calculations in `ChapterNineteenExamples.ExampleNineteenOne` and
  `ExampleNineteenTwo`.  Example 19.1 records the expanded translated circle
  coefficient `b=-6`; Example 19.2 checks `[3,1]` and
  `⟨1:-2:-1:5:-8:0⟩`; Example 19.3 obtains `⟨5:-8:-7⟩` with the exact
  non-singularity disjunction exposed.
- Example 19.4 is `ExampleNineteenFour.example_19_4`.  Every parameter point
  `[t²,2t]` lies on `y²=4x`, and its tangent is equivalent to the normalized
  representative `⟨1:-t:t²⟩`.  `every_point_nonSingular` also proves the
  source's assertion for every incident point when `4 ≠ 0`.
- Exercise 19.1 is `ExerciseNineteenOne.exercise_19_1`, specializing the
  focus/directrix reflection calculation to `y²=4ax`; its companion
  `parabola_coefficients` verifies the displayed equation exactly.
- Exercise 19.2 is `ExerciseNineteenTwo.exercise_19_2`.  The explicit
  intersection of the tangents at `[t₁²,2t₁]` and `[t₂²,2t₂]` is
  `[t₁t₂,t₁+t₂]`, and the quotient-free theorem proves the printed ratio with
  the essential squares on the two `Q(Aᵢ,B)` terms.  `field_eleven_example`
  checks the book's `[1,2]`, `[4,-4]`, `[-2,-1]`, and ratio `5:1` data by
  kernel computation.
- Section 19.3's unnumbered higher-order construction is formalized by the
  finite ten-coefficient `CubicCurve`.  `CubicCurve.taylor_expansion` is the
  exact translated polynomial identity; `tangentLine` and `tangentConic` are
  executable first- and second-order truncations; and
  `tangentLine_is_tangent_to_tangentConic` proves the source's shared-tangent
  assertion.  Both nonsingularity notions remain explicit finite
  disjunctions.
- Examples 19.5–19.6 are represented by the generic folium equation and
  parametrization in `Folium`, plus the ten literal `F₁₃` coordinate
  certificates in `ChapterNineteenFoliumExamples.FieldThirteen`.  Parameters
  `4`, `10`, and `12` have zero denominator by kernel computation.  The
  picture's claim that these exhaust a finite field is intentionally not
  proved by globally enumerating its carrier.
- Example 19.7 checks `[1,-2]`, the printed tangent `⟨2:3:4⟩`, the
  tangent conic `⟨3:3:7:10:1:6⟩`, and all two/four displayed
  intersection witnesses as closed `F₁₃` certificates.  The generic
  theorems `Folium.tangentLine_formula` and
  `Folium.tangentConic_formula_cleared` prove that equations (19.5) and
  (19.6) are exactly the cubic Taylor constructions.
- Example 19.8 is `Folium.four_mul_associatedMatrixDeterminant`, the exact
  quotient-free identity `4 det M=-(t⁶-34t³+1)`.  The two roots
  `17±12r` are proved from an explicit witness `r²=2`, are reciprocal, and
  any supplied cube root annihilates the determinant polynomial.  The real
  interval and decimal classification is outside the finite ordered-field
  boundary.
- Exercise 19.4 is split into its two printed claims.
  `tangentConic_contains_of_parameter_product_cube` proves incidence when
  `(tu)³=1`; `reciprocal_tangent_spreads` proves the reciprocal-parameter
  spread symmetry.  Its four non-null premises expose exactly when those
  rational spreads are defined.
- Section 19.5's lemniscate is formalized as the finite quartic
  `Lemniscate.evaluate`.  `squarePoint_associated` and
  `associatedParameterPoint_contains` prove the associated equation and its
  printed parametrization.  The tangent line and tangent conic formulas are
  executable, contain their base point, and have the same first-order tangent
  by `tangentLine_is_tangent_to_tangentConic`.
- The displayed tangent-conic discriminant is proved in both expanded and
  factored forms.  `discriminantConic` is exactly `8(x²-y²)=A`, and
  `tangentConic_discriminant_eq_zero_iff` proves the source's intersection
  criterion under the necessary `4A≠0` premise.
- Exercise 19.5 is `Lemniscate.inverse_quadrance_product`: if a lemniscate
  point and a discriminant-conic point lie on the same origin line, then the
  exact quotient-free constant is `4 Q(O,P) Q(O,R)=A²`.
- Example 19.9 is proved from explicit witnesses `r₅²=5` and `r₃²=3`.
  The point `[r₅/4,r₃/4]` lies on both curves, its tangent conic has zero
  discriminant, and multiplying the constructed coefficients by eight gives
  the printed `⟨1:2r₅r₃:15:-4r₅:-4r₃:3⟩` exactly.
- Example 19.10 checks the four displayed `F₁₁` intersections, both
  tangent lines and tangent conics, and the focus `[9,9]`/directrix
  `⟨10:5:1⟩` presentation.  The book's final grammola constant contains
  an arithmetic error: its displayed diagonal lines give quadrance sum `1`,
  not `9`.  `tangentConic03_grammola_corrected` proves the valid universal
  `K=1` identity, while `printed_grammola_quadrance_countercheck` refutes
  `K=9` already at the base point `[0,3]`.
- Exercise 19.3 is `Quadrola.reflection`.  The Archimedes equation gives the
  two squared gradient weights; after the mixed terms cancel, their equality
  proves that the gradient tangent makes equal spreads with the two focal
  lines.  The tangent is linked coefficientwise to `Conic.tangentLine` by
  `Quadrola.tangentLine_formula`.  The tangent and two focal lines carry
  explicit non-null premises, precisely because spread need not be defined
  for null directions over a general field.
- All numbered theorems, examples, and exercises in Chapter 19 are now
  formalized, subject to the explicitly recorded source corrections and the
  finite-boundary treatment of decimal plots.

### Chapter 20

- `TriangleSpreadRules.spreadRulerRatio` is the squared height ratio used by
  the spread ruler.  `spreadRulerRatio_complementary` proves complementary
  marks reciprocal away from the endpoints, while `exercise_20_1` proves the
  stronger decidable dichotomy that either a rational label or its complement
  is at most `1/2`.
- `rayRepresentative` is the source's positive affine change of a displayed
  point on a ray.  `sectorTypeScalar_rayRepresentative` proves that changing
  both ray representatives multiplies the acute/obtuse test by the product of
  their positive scales.  `exercise_20_2` consequently proves both type tests
  invariant, making the definitions well-defined.
- `SpreadDifferenceBound` is the two-sided additive form of the source's
  absolute-difference inequality.  `exercise_20_3` covers each choice of two
  supplied bounds and derives the third together with all three acuteness
  inequalities.  `exercise_20_4` proves that three positive quadrances permit
  no pair of obtuse sectors.
- `affineCombinationThree_weights_unique` proves constructively that
  barycentric weights relative to three non-collinear points are unique.
  `affineCircumcenterWeight_nonnegative_iff` identifies the sign of each
  circumcenter weight with the opposite acute-quadrance inequality, and
  `problem_2` proves the solved criterion: a nondegenerate constructive-
  rational triangle is acute exactly when its circumcenter lies on or inside
  the triangle.
- `SpreadRootWitness` retains the finite nonnegative rational square root
  needed by the two roots `littleSpread` and `bigSpread`, without adding a
  completed square-root operation.  `spreadTriple_eq_little_or_big` proves
  these exhaust the Triple spread equation.  `triangle_spread_rule_1` proves
  that the third spread is the big root exactly when the first two sectors are
  acute; its proof explicitly repairs the printed cancellation at the valid
  boundary `s=1`, where the two roots can coincide.  The finite sign identity
  `spreadRoot_product_le_iff_sum_le_one` then yields
  `triangle_spread_rule_2`: the third sector is obtuse exactly when the first
  two are acute and their spreads sum to at most one.  This completes Problem
  3 and Chapter 20.

### Chapter 21

- `problem_4_from_twist_relations` is the finite algebraic core of the
  harmonic-relation problem: the quotient-free forms of equations (21.1) and
  (21.2), together with the collinear quad triple, imply that
  `{1/Q₁,1/Q₂,1/Q₃}` is a quad triple.  The geometric theorem `problem_4`
  constructs those two identities from the displayed base and transversal
  line witnesses, their incidence data, and three altitude conditions by four
  applications of `twist_ratio`.  `twist_eq_of_parallel_pairs` justifies
  replacing each line by the collinear representative used in the other
  right triangle.  Every twist and reciprocal denominator is explicit.
- Problem 5 retains `√154` as the single finite witness `r²=154` rather than
  introducing real numbers.  `problem5ThirdSpread` and
  `problem5QuadranceAE` through `problem5QuadranceDE` are the five exact
  coefficient-pair values printed in the solution.  The initial Cross-law
  values and comparison are `problem_5_initial_spread_certificates` and
  `problem_5_spread_sum_above_one`; `problem_5_quadratic_cleared` and
  `problem_5_triple_spread_cleared` verify equation (21.3) and the selected
  spread root.  `problem_5_spread_law_cleared` verifies both intermediate
  quadrances, and `problem_5_collinear_quadrances_cleared` checks the last two
  by the two required quad triples.  All large expressions are cleared finite
  polynomial certificates over an arbitrary explicit field containing the
  supplied root.
- Problem 6 is `problem_6`.  `eyeball_tangent_spread` performs the first
  Spread-ratio calculation on a displayed tangent ray and proves that changing
  from its tangent point to the marked point on the source circle preserves
  the spread.  `eyeball_chord_quadrance_cleared` performs the midpoint/right-
  triangle calculation and obtains `Q·Q(A,B)=4K₁K₂`.  Applying it to the
  other circle swaps `K₁,K₂`; `problem_6` cancels the explicit nonzero center
  quadrance and proves `Q(A,B)=Q(E,F)`.
- Both solutions to Problem 7 are formalized.  For Solution 1,
  `problem_7_four_point_relation` obtains the literal Euler relation from four
  points, `problem_7_euler_reduction` reduces it to
  `(Q-114)²=80²`, and `problem_7_euler_roots` gives exactly the candidates
  `34` and `194`; `problem_7_solution_one` uses the strict consequence of the
  source's acute bound to select `34`.  For Solution 2,
  `problem_7_spread_certificates` checks all three spread triples and the
  selected value `z=1521/1525` after finite common-denominator clearing.
  `problem_7_two_spread_triples_value` verifies the displayed quotient
  `x=1849/3965`, and `problem_7_solution_two` independently selects `34` from
  `(Q-126)²=92²`.  `problem_7_candidate_bound_certificates` records the two
  closed comparisons supplied by `Q≤126`, while
  `problem_7_selected_value_certificates` verifies the answer in both
  equations.  This completes Chapter 21.

### Chapter 22

- `Vector3`, `Point3`, `Line3`, and `Plane3` provide the chapter's displayed
  three-coordinate geometry.  Their dot product, quadrance, orthogonality,
  direction spread, plane spread, and line-plane spread use only three finite
  coordinates.  `quadrance_add_of_orthogonal` is the spatial Pythagorean
  identity; no dimension cardinality, basis choice, norm completion, or
  square-root operation is imported.
- Problem 8 is `problem_8`.  `box_long_diagonal_metrics` proves that all four
  long diagonals have quadrance `P+Q+R` and computes the three possible dot
  products.  Exercise 22.1 is `exercise_22_1`, giving exactly
  `4P(Q+R)/(P+Q+R)²` and its two cyclic companions.  The numerical
  specialization proves the face/long-diagonal quadrances `7,12`, base spread
  `5/12`, center quadrance `3`, and diagonal spreads
  `3/4,8/9,35/36`.
- `box_center_plane_line_metrics` constructs the denominator-free direction
  of `PF` and normal `R·BC-Q·CG` to `ABP`.  The geometric
  `exercise_22_2_geometric` derives the general spread
  `4QR/((P+Q+R)(Q+R))`; `exercise_22_2` evaluates it to `20/27`.
- Problem 9 is `problem_9_exact`.  Its two right-triangle Spread-law steps
  and final Pythagoras step are retained as cleared integer equations for
  `7350/11`, `595350/209`, and `1619450/209`.
  `problem_9_distance_witness` proves the printed
  `35√276298/209` expression from one supplied square witness, while
  `problem_9_decimal_bracket` certifies by integer comparisons that the exact
  positive distance lies strictly between `88.02` and `88.03` (so the
  source's `88.02` is a truncation).
- Problem 10 is `problem_10`: its square-base diagonal, center and sloping
  quadrances and both Isosceles-triangle calculations are checked after
  clearing their positive integer denominators, yielding `360/529` and the
  adjacent-plane spread `1656/1681`.  Problem 11 is `problem_11`; the three
  displayed right-triangle relations imply the insect's exact horizontal
  spread `S(1-r)` by one explicit nonzero cancellation.
- Problem 12 is `problem_12`.  Substitution of
  `Q₁=P₂+P₃`, `Q₂=P₁+P₃`, and `Q₃=P₁+P₂` into
  Archimedes' function gives the sum of the three right-face quadreas.
  `rightTetrahedronQuadrances_recovered` reconstructs the three leg
  quadrances.  Exercise 22.3 is split into `exercise_22_3_acute`, proving the
  three acute inequalities from positive legs, and
  `exercise_22_3_two_completions`, proving that an explicitly supplied
  nonzero height square has exactly the two signed witnesses `h,-h`.
- Problem 13 is `problem_13`.  A supplied root of the finite cubic factor of
  `S₇` and its selected isosceles root give the exact radial/sloping
  quadrances and the three roof-face spreads.  The source decimals are not
  promoted to real numbers: `problem_13_central_root_certificate` isolates
  the selected cubic root by two integer sign evaluations, and
  `problem_13_decimal_certificates` checks the subsequent displayed decimal
  intervals by integer cross-products.  For Exercise 22.4,
  `scaledFaceAltitude_metrics` proves the exact Gram calculation for the two
  adjacent roof planes, `exercise_22_4_exact` gives their algebraic spread,
  and `exercise_22_4_decimal_certificate` brackets it strictly between
  `0.2243` and `0.2245`.  This completes Chapter 22.

### Chapter 23

- The projectile's landing equation is factored by
  `projectile_landing_factorization`; `projectile_landing_time` selects the
  noninitial root with explicit nonzero data, and
  `projectile_horizontal_quadrance_cleared` gives the displayed
  `g²x²=4a²b²`.  `fixed_sum_product_bound` proves constructively that
  `4AB≤V²` from the nonnegative square `(A-B)²`, while
  `fixed_sum_equal_split` proves equality at `A=B=V/2`.  Problem 14 is
  `problem_14`, recording the maximizing spread `1/2` and maximum horizontal
  quadrance `V²/g²`.
- For Problem 15, `problem_15_lagrange_elimination` starts with the source's
  cleared Lagrange equation and `rc²=1-r`, then derives
  `(2A-V)²=V²(1-r)` without division.  `problem_15` normalizes by the
  explicitly nonzero `V` and obtains `r=4s(1-s)`.
  `problem_15_two_launches` proves that a supplied witness `h²=1-r` exhausts
  the two downhill/uphill values `(1-h)/2,(1+h)/2`; no square-root operation
  or completed real field is introduced.
- Example 23.1 is the executable primitive recursion `fieldElevenStateAt`.
  `fieldElevenStateAt_formula` proves the printed position
  `[t,5t²-2t]` and velocity `[1,3-t]` at every requested finite time;
  `example_23_1_table` checks all twelve displayed columns and
  `fieldElevenStateAt_period` proves period eleven pointwise.  The trajectory
  equation is checked by `fieldElevenTrajectoryPoint_on_curve`, while
  `fieldElevenTrajectory_y_unique` and `fieldElevenTrajectory_chart` give its
  unique vertical coordinate for every supplied horizontal residue label,
  avoiding a global carrier enumeration.  `example_23_1_parabola` proves the
  displayed focus `[9,7]` and directrix `⟨0:1:3⟩` presentation, and
  `example_23_1_vertex` checks `[9,2]`.
- `stationary_quadTriple_derivative` formalizes equations (23.5)--(23.7).
  It exposes the omitted side condition `T₁≠T₂`: after squaring, the
  source cancels the factor `T₁-T₂`, and without this premise (23.7) need
  not follow.  Problem 16 is `problem_16`; substituting the two squared path
  times and their linear derivatives into the corrected stationary equation
  gives the quotient-free Snell relation `V₂s₁=V₁s₂` and hence
  `V₂/V₁=s₂/s₁`.  General analytic existence of an extremum is
  deliberately outside the agreed finite boundary.
- The unnumbered final section is retained exactly.
  `newtonian_velocity_quadTriple` proves equation (23.9).
  `lorentzian_velocity_rearrangement` derives the unsquared polynomial from
  the quotient-free Einstein addition equation, and
  `lorentzian_velocity_squares` proves both equation (23.11) and its fully
  symmetric rewrite.  This completes Chapter 23.

### Chapter 24

- Problem 17 is `problem_17`, the exact complementary Spread-law solution
  `Q=sP/(1-s)` with its denominator premise visible.  Example 24.1 is
  `example_24_1`: its exact coefficient pair is `58700/413`, and integer
  comparisons place it strictly between `142.130` and `142.131`.
- Problem 18 is `problem_18`.  A supplied third root of the Triple-spread
  equation and two cleared Spread-law equations give the inaccessible height
  `s₁s₂Q₃/s₃`.  `surveyingTripleRootNumerator` is the executable
  integer quadratic used for Example 24.2.
  `example_24_2_corrected_certificates` isolates its selected root between
  `0.02790` and `0.02791`, then brackets the resulting quadrances by
  `210.6<Q₁<210.8` and `82.1<Q<82.2`.  Thus the source's `211.5` and
  `82.4` are overly coarse for its own displayed inputs; the exact finite
  certificates retain the corrected values.
- Problem 19 is `problem_19`.  Its two Spread-law/right-triangle
  substitutions prove equations (24.1)--(24.2) after clearing `s₃(1-r)`,
  and the final unknown height remains exactly the selected member of the
  supplied collinear `QuadTriple`.
- For Problem 20, `regiomontanus_spread_rewrite` proves both displayed forms
  of the window spread.  `regiomontanus_denominator_bound` derives
  `2M≤P+M²/P` directly from `(P-M)²/P≥0`; `problem_20` specializes
  `M²=Q₁Q₂` and proves equality at the explicit geometric-mean witness
  `P=M`.  No square-root function is selected.
- Problem 21 is `problem_21`: the three right-triangle height equations are
  substituted into the squared Stewart relation to produce the printed
  quadratic in `H`.  `problem_22_cleared` combines the horizontal Spread law
  with the two vertical right triangles; `problem_22` cancels its explicit
  nonzero denominators to obtain `s₁/r₁-s₂/r₂=s₁-s₂`.
- Problem 23 is `problem_23`.  Its cleared Cross law and two vertical-spread
  equations give `1-s=r₁r₂`.  Exercise 24.1 is `exercise_24_1`, proved
  from the common normalized dot ratio without constructing angles or planes:
  `(1-Sq)²=4(1-S)(1-q)`.  Finally `spherical_pythagoras` converts the
  complementary form following (24.3) into
  `q=q₁+q₂-q₁q₂`.  This completes Chapter 24.

### Chapter 25

- Problem 24 is `ResectionApplications.problem_24_cleared`.  It derives the
  denominator-free centered resection equation
  `(2r₃R₃-Cnum)²=4r₃r₁r₂ A(Q₁,Q₂,Q₃)` from the two
  Spread laws, the Triple-spread relation, and Euler's Four-point relation.
  `problem_24_finish` packages the two Cross-law numerators and final two
  Spread-law equations for `P₁,P₂`; all cancellations carry explicit
  nonzero hypotheses.
- `example_25_1_certificates` checks both displayed `R₃` roots, both pairs
  of Cross-law spreads, and all four resulting `P₁,P₂` values by exact
  common-denominator arithmetic.  `exercise_25_1_triangle_rule_selection`
  checks the four associated spread triples and shows that only the lower
  root has the two obtuse sectors required by the diagram.
  `MatchesResectionReadings` is the direct coordinate alternative requested
  in Exercise 25.2.  `finiteResectionSolutions` filters any explicitly
  supplied finite candidate region, and `exercise_25_2` proves its exact
  soundness and completeness without invoking Euler's relation;
  `example_25_1_direct_reading_certificates` checks the original point
  `[4,5]` by this route.
- The reflected-circle observation following Example 25.1 is represented by
  `ReflectionTriangleData.IsCommonReflectedCirclePoint` and the executable
  `finiteCommonReflectedCirclePoints`.  Its membership theorem and
  `common_reflected_circle_point_unique_in_finite_region` turn a singleton
  search result into an exact uniqueness certificate on the displayed finite
  region.  The book's many-to-one circumcircle case is proved algebraically
  in side-normalized coordinates by
  `circumcircle_reflection_collapses_to_orthocenter_normalized`; cyclic
  relabelling supplies the other two sides.  This is the agreed finite form
  of the cited global common-point construction, rather than an enumeration
  of an ambient infinite plane.
- Problem 25's exact Triangle-spread and Two-spread-triples calculations are
  `problem_25_spread_certificates`.  `problem_25_ratio_certificates` proves
  the Alternate-spreads ratio and its square witness,
  `problem_25_spread_candidates` checks both Spread-from-ratio candidates,
  and `problem_25_final_quadrances` proves the four selected quadrances and
  verifies all five coordinate quadrances of the supplied example.
- Exercise 25.3 is carried through the same complete calculation:
  `exercise_25_3_triangle_spread_certificates` obtains the two missing
  sectors and crossing spread,
  `exercise_25_3_two_spread_certificates` evaluates the two `P` expressions,
  and `exercise_25_3_ratio_certificates` proves the Alternate-spreads ratio
  and exact square witness.  `exercise_25_3_answer_certificates` proves that
  the two printed fractions satisfy the selected Spread-from-ratio equations
  and are proper positive spreads.  This completes Chapter 25 at the finite
  constructive boundary.

### Chapter 26

- `PlatonicSolids.ClearedIsoscelesSpread` is the common denominator-free
  kernel for the five face-spread calculations.  The tetrahedral, cubic,
  octahedral, icosahedral, and dodecahedral results are respectively
  `tetrahedron_face_spread_cleared`,
  `cube_face_and_center_spreads_cleared`,
  `octahedron_face_spread_cleared`,
  `icosahedron_face_spread_cleared`, and
  `dodecahedron_face_spread_cleared`; `platonic_face_spread_summary`
  packages the source-order list `8/9,1,8/9,4/9,4/5`.
  `cube_quadrance_chain_cleared` also records the three Pythagorean cube
  quadrances and `ClearedIsoscelesEndpointSpread` gives the printed `1/3`
  endpoint spread.  `tetrahedron_octahedron_sector_types` retains the exact
  acute/obtuse comparison behind their equal numerical spreads.
- For Exercise 26.1, `regular_tetrahedron_triple_sum_quadrance` proves from
  three displayed edge vectors that their sum has quadrance `6Q`.
  `exercise_26_1` scales this finite identity to the exact cleared formulas
  `3Q(A,G)=2Q` and `8Q(A,P)=3Q`.  `exercise_26_2` compares the actual
  `3Q/8` center-ray isosceles certificate with the `3Q/4` face certificate,
  proving that both spreads are `8/9`.
- Exercise 26.3 is `exercise_26_3`: the order-five quadratic factor at
  `8/9` has exact numerator `-11`, placing the tetrahedral spread below the
  appropriate order-five zero, while the integer cross-product
  `3·9<8·4` places it above the order-six threshold `3/4`.
- The golden identities simplifying the last two solids are
  `Golden.beta_mul_three_alpha_sub_beta_eq_alpha_square` and
  `Golden.five_mul_four_alpha_sub_one_eq_sixteen_alpha_square`, both derived
  from a supplied finite witness `root²=5`.  Exercise 26.4 uses the scaled
  explicit vertices `icosahedronA` through `icosahedronG` and the midpoint
  certificate `icosahedronM_midpoint_cleared`.
  `exercise_26_4_metric_certificates` proves all required quadrances and dot
  products; `exercise_26_4` obtains the two displayed spreads
  `(10-2root)/15`, `(10+2root)/15`, and the long quadrance
  `32(5+root)=(5+root)64/2`.  No square-root selector or completed field is
  introduced.  This completes Chapter 26.

### Chapter 27

- `RationalSphericalCoordinates.PolarCoordinateSquares` is the
  denominator-cleared definition of rational polar coordinates.
  `polar_coordinate_squares`, `polar_jacobian_determinant`, and
  `polar_squared_density` prove equations (27.1)--(27.3) at the finite
  algebraic level, without selecting coordinate signs or square roots.
  The four successive substitutions in Exercise 27.1 are retained as
  `exercise_27_1_substitution_identities`,
  `exercise_27_1_reciprocal_spread`, and
  `exercise_27_1_reciprocal_denominator`.  Their uses in improper integrals
  and endpoint limits are outside the agreed scope.
- Example 27.2 is `example_27_2_lemniscate_cleared`; it derives
  `Q(Q-(2s-1))=0` directly from the Cartesian equation.  The non-origin form
  `Q=2s-1` is `example_27_2_lemniscate`, with the necessary `Q!=0` premise
  explicit.  The claimed area, and Examples 27.1 and 27.3, are integral
  evaluations and hence have no additional finite theorem to encode.
- `PolygonAreaRefinementStep` supplies exactly the two square witnesses used
  at one finite stage of the Archimedean polygon calculation.
  `exercise_27_2_finite_step` is the induction kernel proving that every such
  supplied stage preserves the printed closed pattern;
  `exercise_27_2_first_terms` checks the displayed initial radical
  certificates.  No limiting polygon or completed value of `pi` is formed.
- `SphericalCoordinateSquares`, `spherical_coordinate_squares`,
  `spherical_jacobian_determinant`, and `spherical_squared_density` prove the
  finite content of equations (27.7)--(27.8).  For Example 27.5,
  `example_27_5_cone_sphere_coordinates` derives the two printed region
  equations `q=1/2` and `R=1-q` from the cone and projective-sphere
  equations.  The final volume integral is deliberately not represented.
- The exact endpoint algebra used by the remaining three-dimensional examples
  is retained separately: `examples_27_6_27_11_cap_factorization` covers the
  common spherical/hyperbolic cap polynomial in Examples 27.6 and 27.11;
  `examples_27_7_27_12_ring_endpoint` covers the common sphere/hyperboloid
  ring numerator in Examples 27.7 and 27.12; and
  `example_27_8_paraboloid_endpoint` covers Example 27.8.
  `example_27_9_hemisphere_centroid` proves the exact centroid height `3/8`
  after the two displayed mass and moment evaluations are supplied.
  `example_27_10_beta_coefficient` proves the finite Gamma-recurrence
  calculation `B(2,1/2)=4/3`.  The surrounding integral and square-root
  evaluations in Examples 27.4--27.13 are outside the finite boundary.
- `example_27_14_surface_cap_cleared` retains the linear surface-cap endpoint
  simplification.  In four dimensions,
  `FourSphericalCoordinateSquares`, `four_spherical_coordinate_squares`,
  `four_spherical_jacobian_determinant`, and
  `four_spherical_squared_density` prove equation (27.9) and the printed
  determinant/density identities.  `example_27_15_beta_coefficient` proves
  its finite recurrence arithmetic `2B(3/2,1/2)=Gamma(1/2)^2`.  The
  four-dimensional ball integral and Exercise 27.3's surface-volume integral
  are excluded by the same agreed boundary.  Thus every finite algebraic
  derivation in Chapter 27 is represented, while no exponential, improper
  integral, infinite limit, or completed real constant is introduced.

### Appendix A

- `RationalPolarCatalogue.PolarCoordinateSquares` reuses Chapter 27's
  denominator-cleared coordinate interface.  The central circle, line,
  ellipse, and hyperbola conversions are respectively
  `circle_rational_polar`, `line_rational_polar_cleared`,
  `ellipse_rational_polar`, and `hyperbola_rational_polar`.  Every division
  by a nonzero radial quadrance is exposed as a premise.
- The parabola conversion is proved first in the origin-safe factored form
  `parabola_rational_polar_origin_safe`, then as the printed non-origin form
  in `parabola_rational_polar`; `parabola_centered_rational_polar` proves its
  displayed completed-square rewrite.  `cardioid_rational_polar_cleared`
  handles both orientations by an explicitly supplied signed horizontal
  coordinate.  `limacon_rational_polar_cleared` derives the limacon equation
  from finite radial, cosine, and parameter square witnesses, and
  `limacon_specializes_to_cardioid` proves its cardioid specialization.
- Setting the two limacon parameters equal yields the minus-sign equation in
  `trisectrix_rational_polar_cleared`.  The source instead prints a plus sign;
  `printed_trisectrix_counterexample` checks at `A=1,Q=9,s=1` that the
  corrected equation holds while the printed equation fails.
- The even-curve eliminations are `astroid_rational_polar_cleared` and
  `eight_curve_rational_polar_cleared`.  For the bullet nose, completing the
  preceding quadratic gives `bullet_nose_rational_polar_corrected`; the
  source's displayed right side is four times too large.
  `printed_bullet_nose_counterexample` proves this discrepancy on exact
  rational polar data.
- `deltoid_rational_polar_cleared` squares the single odd Cartesian term and
  derives the printed third-spread-polynomial equation.  The hippopede's
  displayed Cartesian equation gives `hippopede_rational_polar_corrected`,
  namely `4B²s=Q+4B(B-A)`, not the printed `4Bs=Q+4B(B-A)`;
  `printed_hippopede_counterexample` checks both the Cartesian and corrected
  equations and refutes the printed one at `A=1,B=4,Q=16,s=1`.
- The final two calculations are
  `bernoulli_lemniscate_rational_polar`, with Appendix A's factor-two
  normalization, and `folium_rational_polar`.  The latter performs both
  finite squarings and cancellations needed to eliminate the odd product
  `xy` and obtains the full printed degree-six polynomial.  Thus every
  Appendix A catalogue entry and every derivation left to the reader is
  represented over arbitrary explicit fields, with the three source errors
  recorded as corrected rather than silently assumed.

### Appendix B

- `Ellipson.polynomial` and `Ellipson.Contains` encode the defining
  Triple-spread surface.  `polynomial_permutations` and
  `contains_permutations` prove its full sixfold coordinate-permutation
  symmetry.  `tetrahedron_vertices` checks the four printed cube vertices;
  `tetrahedron_oriented_six_volume` computes the edge determinant `-2`, and
  `tetrahedron_volume_certificate` records the denominator-cleared
  `2/6=1/3` volume calculation.
- `OnCubeBoundary` is the order-free algebraic union of the six unit-cube
  faces, while `OnTetrahedronEdge` is the union of the six displayed
  tetrahedral edges.  The six lemmas from `x_zero_face_square` through
  `z_one_face_square` compute every face restriction.  Over any explicit
  field with decidable equality, `cube_boundary_intersection` proves the
  exact biconditional: an ellipson point is on a cube face if and only if it
  is on one of those tetrahedral edges.  Thus the source's “precisely a
  tetrahedron” statement is captured without an ordered ambient continuum.
- `CoordinateCrossSection` is the fixed-coordinate quadratic derived by
  `fixed_third_cross_section`; `all_coordinate_cross_sections` transports it
  to all three coordinate directions.  `coordinate_cross_section_centered`
  diagonalizes it as
  `c(x+y-1)²+(1-c)(x-y)²=c(1-c)`.  The four boundary-square lemmas and
  `coordinate_cross_section_tangencies` prove the four double roots which
  give the printed tangency to the unit square.
- `PlaneTwoCrossSection` and `plane_two_cross_section` substitute the
  oblique plane `x+y+z=2` directly into the ellipson.  The book does not give
  its subsequent planar coordinate change, so `ObliqueCoordinateCurve`
  records the displayed suitable-coordinate equation after multiplying by
  six.  From a supplied finite witness `root²=6`,
  `oblique_rational_polar_cleared` derives exactly
  `(6Q)³s(3-4s)²=(36Q-5)²`, and
  `oblique_left_is_third_spread_polynomial` identifies the left factor with
  `S₃(s)`.
- Exercise B.1 is explicitly labelled “requires calculus” and asks for the
  analytic volume `pi²/16`.  By the agreed finite boundary, no volume
  integral or completed real constant is introduced.  All finite algebraic
  data used to pose that region—the surface, its cube boundary, its sections,
  and its exact rational-polar conversion—has been formalized above.

This completes the source-numbered finite constructive coverage inventory.
