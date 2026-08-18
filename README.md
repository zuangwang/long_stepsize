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
```

## Results

Store durable outputs in `results/` and document the command and parameters
that generated each result. Results are tracked by default and must not be
silently deleted or overwritten. Regenerable scratch outputs should remain
untracked under `tmp/` or `scratch/`.

Before making changes, read the repository [agent instructions](AGENTS.md).
