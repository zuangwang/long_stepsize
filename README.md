# gd

`gd` is a Julia project for implementing and evaluating gradient-descent
methods and related optimization experiments.

## Layout

- `src/GD.jl`: maintained Julia package source.
- `results/`: durable outputs from validated runs.
- `agents/`: agent instructions, task briefs, reports, and relay artifacts.

The initial repository contains a loadable package namespace and project
infrastructure. Algorithm implementations will be added when their requirements
are defined.

## Requirements

- Julia 1.12 or newer in the 1.x series.
- Lean 4.32.2 (managed by `elan` through `lean-toolchain`).

## Setup

From the repository root, instantiate the project environment:

```bash
julia --project=. -e 'using Pkg; Pkg.instantiate()'
```

## Run

Load the package with:

```bash
julia --project=. -e 'using GD'
```

## Validation

```bash
julia --project=. -e 'using GD'
lake build
```

## Lean formalization

The Lean development formalizes the quantitative proof in
[`results/sqrt3_lower_bound_report.tex`](results/sqrt3_lower_bound_report.tex).
Import [`GD/Sqrt3LowerBound.lean`](GD/Sqrt3LowerBound.lean) for the complete
theorem collection, or [`GD.lean`](GD.lean) for the package root.

| Report component | Lean module | Principal declarations |
| --- | --- | --- |
| Two-state entropy inequality | `Entropy.lean` | `twoState_blockScale`, `scalar_entropy` |
| Exact temporal inverse product and half-density bound | `TemporalProduct.lean` | `exactTemporalProduct`, `globalTemporalProduct`, `halfDensityCertificate` |
| Neighboring cutoffs and endpoint Lyapunov drift | `RankCutoff.lean` | `rankMass_ratio`, `rankDensity_recurrence`, `oneStepLyapunovDrift` |
| Tail-budget transport | `RankCutoff.lean` | `coreTailBudgetTransport`, `tailBudgetTransport` |
| Concrete schedule, chronological chains, and scalar contribution | `Schedule.lean` | `scheduleChainData`, `scheduleChainData_contribution`, `HasChainContribution` |
| Schedule normalization and half-density witness | `ScheduleNormalization.lean`, `ScheduleCertificate.lean` | `normalizedChainContribution`, `scheduleHalfDensityContribution` |
| Bounded-rank finite-prefix witness | `FinitePrefix.lean` | `scheduleFiniteCutoffContribution` |
| Finite constant, witness-preserving scan, and horizon | `Certificate.lean` | `uniformFiniteCutoffConstant`, `completeCutoffScan_mono`, `scheduleHorizonContribution` |
| Explicit universal constant | `Certificate.lean` | `explicitLowerBoundConstant` |
| Finite-polytope Moreau envelope | `MoreauEnvelope.lean` | `finiteEnvelope_hasGradient`, `finiteEnvelope_one_smooth` |
| Marked-stage geometry and exact projections | `MarkedStage.lean` | `internalProjection`, `terminalProjection`, `finalEnvelopeGap` |
| Literal GD trajectory for a selected chain | `ScheduleTrajectory.lean` | `scheduleState_step`, `chainNormalizedInstance` |
| Prescribed initialization and physical scaling | `UniversalTheorem.lean` | `physicalize`, `universalSqrtThreeLowerBound` |

All checked declarations are theorem proofs over Mathlib: the development
contains no `sorry`, `admit`, or project axioms.  The final theorem
`universalSqrtThreeLowerBound` is unconditional apart from the hypotheses in
the paper (`T ≥ 1`, `L,R > 0`, and a nonnegative predetermined schedule).  It
constructs a dimension `d ≤ T + 1`; for every prescribed initial point it
constructs a convex differentiable objective with `L`-Lipschitz gradient, a
minimizer at distance `R`, the literal GD trajectory, and the claimed
last-iterate gap with the explicit positive universal constant.

## Results

Store durable outputs in `results/` and document the command and parameters
that generated each result. Results are tracked by default and must not be
silently deleted or overwritten. Regenerable scratch outputs should remain
untracked under `tmp/` or `scratch/`.

Before making changes, read the repository [agent instructions](AGENTS.md).
