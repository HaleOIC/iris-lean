# IAesopTest

Standalone Lake package for evaluating the local `iaesop` tactic from
`iris-lean` on two case studies:

- `IAesopTest`: tactic-focused copies of Iris examples and tests.
- `IrisITree`: the Iris interaction-tree development imported from the local
  `wpi` branch as a second case study.

Running `lake build` builds both libraries. `IrisITree` additionally uses the
`ISTA-PLV/Coinductive` package at the revision recorded in `lake-manifest.json`.
