# Pollack–Daboussi elementary PNT argument

Public repository: https://github.com/twonth/daboussi-pnt-lean

The bundled manuscript is the final supplied revision with the Lean availability
statement inserted. Its smooth-number cutoff is **y ≥ 2**, as already supported
by the formalization. All Lean sources are unchanged from the verified build.

This project formalizes Theorem 1 of Paul Pollack's supplied manuscript,
**M(x) = o(x)**, following its smooth-number proof. The manuscript is preserved
in `paper.tex`. Its cited equivalence with the prime-counting formulation of
the PNT is not separately proved here.

`Challenge.lean` is a 12-line statement using mathlib's Möbius function.
`Solution.lean` proves exactly that statement. There are **no proof gaps or
added axioms** in the solution or its supporting modules. The only `sorry`
is the intentional placeholder in the independent challenge file. The main
theorem's transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Proof map

All declarations below are in namespace `Daboussi`.

| Paper step | Lean declaration | File in `Daboussi/` |
|---|---|---|
| §2 harmonic bound | `harmonic_mobius_bound` | `Arithmetic.lean` |
| Equation (signed) | `signed_integral_bound` | `SignedIntegral.lean` |
| Constant sign and a small value in [X,BX] | `M_constant_sign`, `exists_small_value` | `Steps.lean`, `SmallValues.lean` |
| Disjoint geometric blocks | `block_deficit_growth` | `Blocks.lean` |
| Equation (support) | `smoothM_support` | `SmoothSupport.lean` |
| Smooth/rough factorization | `M_split` | `SmoothConvolution.lean` |
| Coprime counting and constant bands | `rough_interval_le`, `abs_M_le_bands` | `CoprimeCounting.lean`, `FloorBands.lean` |
| Equation (positive-mass) | `smooth_mass_eq_euler_product` | `SmoothMass.lean` |
| Proposition 3 | `smooth_comparison` | `Comparison.lean` |
| §3 deficit reduction | `deficit_control` | `DeficitControl.lean` |
| Equation (below) | `below_excess_small` | `BelowIntegral.lean` |
| Smooth logarithmic identities | `smoothM_log_identity`, `psi_log_identity` | `SmoothLogarithms.lean` |
| Equation (excess-inequality) | `excess_recurrence` | `ExcessRecurrence.lean` |
| Changes of integration order and variables | `excess_average_mass`, `scaled_excess_mass` | `ExcessFubini.lean`, `ExcessScaling.lean` |
| Integrated recurrence | `excess_moment_le_coefficient` | `ExcessMoment.lean` |
| Mertens bounds | `mertens_product_upper`, `mertens_coefficient_upper` | `MertensProduct.lean`, `MertensCoefficient.lean` |
| Centered moment and three ranges | `three_range_integral_bound` | `ThreeRanges.lean` |
| Equation (excess-goal) | `smooth_excess_small` | `ExcessEstimate.lean` |
| Fundamental Lemma and a = 0 | `fundamental_lemma`, `limsup_eq_zero` | `Fundamental.lean` |
| Theorem 1 | `mobius_summatory_limit` | `../Solution.lean` |

## Fidelity

The dependency chain is the paper's: smooth comparison → excess recurrence →
weighted moment → three ranges → Fundamental Lemma → signed-integral and
geometric-block contradiction. No existing PNT or Möbius cancellation theorem
supplies the conclusion. No complex-analytic PNT argument, Selberg symmetry
formula, or Dickman estimate replaces a step.

Technical reorganizations are explicit:

- Smoothness uses bounds on prime divisors, and prime-power sums use the
  smooth restriction of von Mangoldt. Dirichlet convolution establishes the
  same smooth/rough identity.
- The positive-mass identity is proved directly by Tonelli on the kernels
  `1_[n,∞)(t)/t²`, followed by the smooth Euler-product expansion. This replaces
  the intermediate partial summation and polylogarithmic growth bound for Ψ.
- Primorial support allows a finite prime-power sum when integrating the
  recurrence; its coefficient is bounded by the full geometric series.
  Integrability is proved explicitly throughout.
- The centered moment and three ranges are combined into an indicator-function
  majorant before integration. The split point `exp ((1+ε) log y)` equals
  `y^(1+ε)`.
- The below-cutoff proof absorbs the floor error into ε/2 by enlarging T.
  General scalar/filter and geometric-block lemmas organize the final limits.
- The main statement uses convergence of M(x)/x to zero instead of little-o.

## Build and audit

Lean and mathlib are pinned in `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. With the matching toolchain:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean MainAudit.lean
lake comparator --config comparator.json
```

The comparator configuration allows only the three standard axioms. The
linked comparator project is included in Lean 4.35 as `lake comparator`;
its isolated build mode requires Linux and bubblewrap. The local Windows
exported-proof comparison and kernel replay passed (exit code 0). This run
uses `--inadvisably-no-sandbox`, and therefore does
not establish isolation against adversarial build code. See its full log in
`Verification/comparator.log`. Exports include the configured theorem,
permitted axioms, and the bundled comparator's primitive targets.

`verify-local.ps1` compiles every source module in dependency order against
an existing pinned mathlib cache and saves logs in `Verification`. It audits
169 supporting declarations and the main theorem for forbidden dependencies.
Only the challenge placeholder is allowed. The script does not modify the
external mathlib cache. A fresh network download of all Lake dependencies
is not part of the local verification.

## Provenance and review

`MertensUpper.lean` is the unchanged local elementary Mertens development,
recompiled from source; see `vendor-provenance.json` and `vendor-licenses`.
Further product and prime-power estimates are proved in this project.
`formalization.yaml` follows schema v0.4. Compiler and axiom checks do not
constitute independent peer review or author endorsement.
