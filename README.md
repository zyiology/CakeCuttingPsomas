# cake-cutting-psomas

A Lean formalization in progress of Alexandros Psomas's
*Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol*.
The original TeX source is in [paper/main.tex](paper/main.tex).

Sections 2–3's recursive protocol, `Dominate` construction, and explicit query
bound are proved conditional on correct `Core` and `Repair` subroutines.
**The unconditional target theorem is unproved** and contains `sorry`;
`Core` is constructed conditional on a correct `Permute` protocol;
`Repair` and `Permute` remain to be implemented.

Run `lake build` to check the project using the pinned Lean and mathlib versions.
See [the formalization guide](docs/formalization.md) for the statement, file map,
and remaining work.
