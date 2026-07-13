# SFS-sysml.library

Supplemental Formal Semantics (SFS) for KerML and SysML v2 — a modified fork of the OMG `sysml.library`.

## Structure

- **SFS content** lives in `sysml.library/Kernel Libraries/Kernel Semantic Library/SFS library/` (6 `.kerml` + 2 `.sysml` files).
- SFS also **modifies standard library files** in-place (e.g., `KerML.kerml`, `Occurrences.kerml`). Look for `//SFS` comments in those files.
- Standard library files mirror `Systems-Modeling/SysML-v2-Release` upstream.

## Tooling

- Built with **Syside** (Sensmetry). Config: `syside.toml` at repo root.
- Format: `line-width=100`, `tab-width=2`, `tabs=false`.
- Lint: `standard-library-package = "warning"` (expect warnings in SFS-modified standard files).
- No build/test/lint/typecheck scripts — this is a modeling library, not a code project.
- Eclipse Xtext project (`.project`, `.settings/`) for IDE use.

## Conventions

- **Use `@Assert` metadata** (from `Assert.sysml`) for formal annotations. Do **not** use the older `language "Domain"` annotation style or `Assertion::Assert` (KerML metaclass in `Assertion.kerml` — deprecated).
- `Domain::Instant` specializes `ISQSpaceTime::TimeValue`, not `Real`.
- `.index.json` is **auto-generated** (280k+ lines) — do not hand-edit.
- `.gitignore` excludes `/bin/` and `/output/`.

## Workspace URIs (from `.workspace.json`)

| URI | Path |
|-----|------|
| `urn:kpar:Kernel-Data-Type-Library` | `Kernel Libraries/Kernel Data Type Library/` |
| `urn:kpar:Kernel-Function-Library` | `Kernel Libraries/Kernel Function Library/` |
| `urn:kpar:Kernel-Semantic-Library` | `Kernel Libraries/Kernel Semantic Library/` |
| `urn:kpar:SysML-Systems-Library` | `Systems Library/` |
| `urn:kpar:SysML-<Domain>-Library` | `Domain Libraries/<Domain>/` |

## Commands

```bash
# Use Syside with this library (from repo root):
#   syside
# Or redirect a project to use this library via syside.toml:
#   std = "/path/to/SFS-sysml.library/sysml.library"
```
