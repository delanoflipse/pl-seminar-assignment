# Project - CS4130 Seminar Programming Languages

This repository contains the source code for the final project of the course [CS4130 - Programming Languages Seminar](https://www.studiegids.tudelft.nl/a101_displayCourse.do?course_id=64366).

## Monadic Compiler Calculation

This project works on the results presented in the paper [Monadic Compiler Calculation by Bahr and Hutton (2022)](https://dl.acm.org/doi/abs/10.1145/3547624). This paper extends earlier work on compiler calculation to capture non-termination and non-determinism with the help of monads. Using monadic structures in the definition of the source language and correctness proofs allows for a total formulation that can be mechanically verified, with the additional benefit of having the ability to use the monadic laws in equational reasoning.

## Project Goal

The paper primarily uses two monads: The _Partiality_ monad (Section 2 and 3) and the _ND_ (Section 4) monad, which capture non-termination and non-determinism respectively. In the last section (Section 4.6), the paper combines them into a _PND_ monad, which requires a specific definition, and a rework of the proof.

The goal of this project is to investigate whether we can define the _Partiality_ and _ND_ monads as free monads, and combine them into a _PND_ monad by taking the coproduct of the two monads, which for free monads is well defined.

The paper contains an artefact that formalises the paper’s results in [Agda](https://github.com/agda/agda) for all three monads. We will be defining the two monads using the free monadic structure, and then rewriting the existing proofs for the free monads.

## Findings

- Defining free monads in their most common definition is not possible due to Agda's strict positivity checker. Instead, we can use Containers (or Effects) to define impure side-effects as a tuple of a side-effect type and a continuation function.
- Adjusting the theorems requires effort, as case analysis on each monadic type used to be simple data structures, but reasoning about the continuations requires function extensionality, which means we need to provide the type checker with more clues to be able to distinguish cases.
- The _Partiality_ monad is coinductively defined, so even though we can define it as a container/effect, applications of it will not always pass the termination checker. The original work already defined the monad as mutually (co)inductive to work around this, and we need a coinductive definition of the Free monad to complete the mechanical proof.
- The theorems for the _Non-Determinism_ monad in part rely on the fact that it is inductively defined and therefore each operator can only be deconstructed into a smaller part. Agda does not fully recognise this for free monadic structure and therefore some adjusted proofs do not pass the strict positivity checker, although they should be terminating.
- Adjusting the compiler calculation correctness proofs required little adjustments, only requiring the addition of a few explicit bisimilarity steps.
- Due to being a novice at Agda, I opted to use the `--type-in-type` flag to resolve issues with type universes. Removing this flag will take effort.
- The learning curve to learn Agda, when already familiar with Coq, is still quite steep. Starting with non-trivial proofs does not make it easier to get the hang of it. I needed to work on a few learning exercises (which are included in the extras) before adjusting to defining proofs in Agda.

The lib directory contains the theorems for the _Non-Determinism_ monad defined as a free monad. Due to challenges arising from having to define the _Partiality_ monad as coinductive and time constraints, I was unable to complete all theorems for this monad. The following points are therefore speculations about the original goal of the project:

- The definition of bisimilarity (~) has two different definitions based on the monads used. This definition does not seem to trivially follow from the free monadic structure, and would require another adjustment of the theorems to incorporate a single definition.
- The current adjustments are only for a single free monad, but do not account for a disjoint sum of one or more containers/effects. With the help of smart constructors, this would be a bit simpler, but this requires _another_ rewrite of the theorems.
- I am unsure how possible it would be to combine a coinductive and inductive free monad.

## Project structure

The main project resides in the `lib` directory. The project includes a git submodule to the original artefact for ease of access but is not required for the final implementation. The `lib/FreeMonads` directory defines the structure for free monads (in the `Structure` subdirectory), specific instances of the free monads and the adjusted theorems (in the `Theorems` subdirectory) for the monads defined as free monads. In the `lib/Languages` directory we can find the adjusted theorems applied to a compiler calculation used in the original paper. These apply both the adjusted monads and theorems, so they can be seen as the main result of this project.

## Disclaimer

To assist me in this project I have used AI technologies. As Agda was new to me, I have used ChatGPT to explain how the Agda syntax works and help me read and understand the existing proofs. I additionally use Github Copilot to reduce keystrokes (to prevent RSI), although the suggestions for Agda often resulted in incorrect code so this was often impractical.
