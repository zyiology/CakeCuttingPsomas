# cake-cutting-psomas

A Lean formalization in progress of Alexandros Psomas's
*Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol*.
The original TeX source is in [paper/main.tex](paper/main.tex).

The normalized unit-cake main theorem is proved: for every positive number `n`
of agents, one Robertson–Webb protocol returns a complete envy-free allocation
using at most `2 * 32^n * n^7 * (n!)^2` queries. The construction assembles
Sections 2–5's `Divide`, `Dominate`, `Core`, `Repair`, and `Permute` protocols.
The separate asymptotic corollary remains to be formalized.

Run `lake build` to check the project using the pinned Lean and mathlib versions.
See [the formalization guide](docs/formalization.md) for the statement, file map,
and remaining work.
