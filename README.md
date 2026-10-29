# cake-cutting-psomas

A Lean formalization in progress of Alexandros Psomas's
*Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol*.
The original TeX source is in [paper/main.tex](paper/main.tex).

Section 2's recursive protocol and explicit query bound are proved conditional
on a correct `Dominate` subroutine. **The unconditional target theorem is
unproved** and contains `sorry`; `Dominate` remains to be implemented.

Run `lake build` to check the project using the pinned Lean and mathlib versions.
See [the formalization guide](docs/formalization.md) for the statement, file map,
and remaining work.
