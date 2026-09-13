# Repository conventions

This is a public mathematical formalization. Use compact, precise prose,
standard notation, and descriptive filenames. Explain the physics for readers
with limited programming experience. Avoid invented terminology and decorative
formatting. Follow `CONTRIBUTING.md`.

The full common-domain statement and proof are in
`Adiabatic/Unbounded/Statement.lean` and `Adiabatic/Unbounded/MainTheorem.lean`.
The original finite-dimensional statement and proof remain in
`Adiabatic/Statement.lean` and `Adiabatic/MainTheorem.lean`. Preserve their
meaning when refactoring.
Do not add unfinished proofs, new axioms, unsafe declarations, or native
decision procedures. Check both compilation and transitive theorem axioms.

Keep verified results distinct from proposed extensions. Update the proof
guide and verification note when the theorem's scope changes. Do not claim
that a search proves no prior formalization exists.

Use `main` for checked work. Keep experiments in an explicitly named branch.
Do not publish or push without the repository owner's instruction.
