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
| Finite constant, complete scan, horizon, and scaling | `Certificate.lean` | `uniformFiniteCutoffConstant`, `completeCutoffScan`, `normalizedHorizonBound`, `physicalScalingBound` |
| Explicit universal constant | `Certificate.lean` | `explicitLowerBoundConstant` |
| Marked-stage terminal algebra and proof composition | `Realization.lean` | `markedStageRealizedGap_of_rho`, `sqrtThreeLowerBound_from_certificate` |

All checked declarations are constructive theorem proofs over Mathlib: the
development contains no `sorry`, `admit`, or project axioms.  The realization
module checks the exact marked-stage amplitude and terminal Moreau-envelope
value algebra.  Its final composition theorem exposes the two scalar
certificate obligations explicitly, matching the temporal-product and
finite-prefix branches of the report.

## Results

Store durable outputs in `results/` and document the command and parameters
that generated each result. Results are tracked by default and must not be
silently deleted or overwritten. Regenerable scratch outputs should remain
untracked under `tmp/` or `scratch/`.

Before making changes, read the repository [agent instructions](AGENTS.md).
