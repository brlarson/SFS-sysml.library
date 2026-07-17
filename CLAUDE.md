# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repository is

SFS-sysml.library is a modified fork of the OMG `sysml.library` — the standard library of KerML and SysML v2
files. It adds **Supplemental Formal Semantics (SFS)**: formal, machine-checkable annotations layered onto the
standard library's informal definitions. This is a modeling library, not a software project — there is no
build, test, or lint tooling in the traditional sense.

## Repository structure

- `sysml.library/Kernel Libraries/Kernel Semantic Library/SFS library/` — the SFS-specific content (net-new
  `.kerml`/`.sysml` files: `Allen.kerml`, `Assert.sysml`, `Assertion.kerml`, `Domain.kerml`,
  `ItemPortInterface.sysml`, `Mereology.kerml`, `Regions.kerml`, `RunTimeServices.kerml`).
- Everywhere else under `sysml.library/` (`Kernel Libraries/`, `Domain Libraries/`, `Systems Library/`) mirrors
  the upstream `Systems-Modeling/SysML-v2-Release` standard library, **with in-place SFS modifications**.
  Modified lines/blocks are marked with a `//SFS` comment (e.g. `//SFS: fundamental change of Occurrence to be
  Interval`, `//SFS new`) — grep for `//SFS` to find every place the standard library was altered and read the
  adjacent comment for the rationale.
- `.workspace.json` defines the Syside project layout: each subfolder under `Domain Libraries/` and
  `Kernel Libraries/`, plus `Systems Library/`, is its own project with a `urn:kpar:...` IRI. Use this file to
  understand which files logically group together.
- `sysml.library/.index.json` is auto-generated (280k+ lines) — never hand-edit it.
- `AGENTS.md` at the repo root duplicates most of this guidance for other coding agents; keep the two in sync
  if conventions change.

## Core convention: `@Assert` metadata

Formal annotations attach a `Domain`-logic formula string to an element via `@Assert`/`@Invariant`. There
are **two parallel definitions, one per source language** — use whichever matches the file you're editing:

- **`.kerml` files** import and use `Assertion::Assert` (a `metaclass` in `Assertion.kerml`), because KerML
  has no `metadata def` construct.
- **`.sysml` files** import and use `Assert::Assert` (a `metadata def` in `Assert.sysml`).

Both declare the same shape:

```
attribute n[0..1] : String;  // name
attribute f[1..*] : String;  // formula(s)
attribute t[0..*] : String;  // theorem name(s) attesting to this @Assert
```

Applied identically either way:

```
@Assert{n="Get"; f="<<Get : d~Occurrence, f~Anything, tau~Instant := I[[d::f,tau]] >>"; t="df-model";}
```

- **Always use `@Assert`/`@Invariant`** for new formal annotations — pick `Assertion::Assert` or
  `Assert::Assert` by file extension as above, not by "which is newer."
- **Do not** use the older `language "Domain" ...;` string-annotation style (legacy, being phased out — see
  recent commit history converting `language "Domain"` usages to `@Assert`).
- Formulas (`f=`) are plain strings using `<< >>` delimiters for the formal notation; multiple formulas or
  theorem names are given as a tuple, e.g. `t=("df-model","df-bl.nowrr")`.
- The formula language itself (`<<Name : var~Type, ... : body>>`, `I[[...]]`, `forall`/`exists`, etc.) is
  defined in `~/git4/Supplemental-Semantics/Main/Supplemental-Semantics.pdf`, Appendix J ("Domain Logic")
  and §3.13.1 ("Extending Expression for SFS").
- The `<<Name : var~Type, ... : body>>` header only needs to declare identifiers that aren't otherwise
  resolvable. An identifier already visible in the lexical scope where the `@Assert` appears — e.g. an
  `in`/`out feature` of the same (or an inherited) behavior/function the annotation is attached to — does
  **not** need to be re-listed as a formula parameter; only genuinely free variables (nothing in scope
  matches the name) need `forall`/`exists` quantification or a header declaration.

## Other domain conventions

- `Domain::Instant` specializes `ISQSpaceTime::TimeValue`, not `Real` — don't reintroduce a raw numeric `Time`
  type.
- Transfers between features/ports must remain conforming per SysML v2 §8.4.13.6 semantics (see the
  `AcceptPerformance`/`Transfers.kerml` commit history for an example of a correction here).

## Tooling (Syside)

- The library is developed and edited with **Syside** (Sensmetry). Config lives in `syside.toml` at the repo
  root.
- To use this fork's library from another Syside project, set in that project's `syside.toml`:
  `std = "/path/to/SFS-sysml.library/sysml.library"`.
- Formatting: `line-width = 100`, `tab-width = 2`, `tabs = false` (see `[format]` in `syside.toml`).
- Linting: `standard-library-package = "warning"` — expect (and ignore) this warning on every SFS-modified
  standard library file, since editing standard-library packages is exactly what this repo does.
- `.gitignore` excludes `/bin/` and `/output/` (Syside build artifacts).
- There is also an Eclipse Xtext project setup (`.project`, `sysml.library/.settings/`) for IDE use, but Syside
  is the primary tool.
