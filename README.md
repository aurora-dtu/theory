# AuRoRA Theory

[![GitHub CI](https://github.com/aurora-dtu/theory/actions/workflows/docs.yml/badge.svg)](https://github.com/aurora-dtu/theory/actions/workflows/docs.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/aurora-dtu/theory)

This repository holds Lean formalization of prior and ongoing work under the AuRoRA project.

The best way to explore the project is by visiting the [documentation](https://aurora-dtu.github.io/theory/) or reading one of the [publications](#Publications).

## Building the project

To build the project, one needs Lean installed. The recommended approach is to use VS Code as listed [here](https://lean-lang.org/lean4/doc/quickstart.html). If you prefer the CLI, then install [elan](https://github.com/leanprover/elan?tab=readme-ov-file#installation) and run `lake build`.

## Formalizations efforts

- **_Markov Decision Processes_ (MDP)** [[Docs](https://aurora-dtu.github.io/theory/MDP.html)]
    - Formalization of countably infinite branching MDP.
    - Optimal expected cost of MDPs.
    - Fixed point formalization of expected cost and relation to finitly branching MDPs.
    - Connecting different interpretations of optimal expected cost across optimization order and history-dependence.
- **_probobalistic Guarded Command Language_ (pGCL)** [[Docs](https://aurora-dtu.github.io/theory/PGCL.html)]
    - Definition of a variant of pGCL and it's operational semantics.
    - The induced MDP of the operational semantics of pGCL to define expected costs of programs.
    - Connecting the _Weakest Preexpectation_ (WP) of pGCL programs to the optimal expected cost of the induced operational MDP by way of least fixed points.

## Publications

- _More to come..._
