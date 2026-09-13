# Contributing

Use standard mathematical terminology, descriptive filenames, and compact
prose. Explain the assumptions and physical meaning before implementation
details. Use GitHub-rendered LaTeX for mathematics in Markdown.
Avoid promotional language, conversational asides, and repeated assurances.
Retain assumptions, quantifiers, citations, and scope limitations.

Keep proofs readable and use existing mathlib results where possible.
An estimate, propagator, or spectral construction must be derived if the
theorem claims to establish it. Do not replace missing work with assumptions
that contain the conclusion.

Run `lake --wfail build` and `python3 checks/check_proofs.py` before submitting
a change. When changing the integrity checker, also run
`python3 -m unittest discover -s checks -p 'test_*.py'`. Add substantive new
public theorems to the named axiom reports. Keep the formal statement, proof
guide, and verification note consistent. Record
changes in `UPDATES.md` with their mathematical scope and checks.

Preserve attribution when adapting existing proofs. Keep dependency caches,
compiler output, personal notes, and machine-specific paths out of Git.
Contributions use the repository's Apache 2.0 license.
