# cake-cutting-psomas

A Lean formalization of Alexandros Psomas's
*Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol*.
The original TeX source is in [paper/main.tex](paper/main.tex), taken from https://arxiv.org/abs/2610.30370

Disclaimer: This entire process was handled by Codex using GPT-6.1-Sol medium, I have not verified the results. I just wanted to see what the process looks like, and seems like Codex handled everything pretty smoothly. I just asked it to break down each section into a set of milestones, and implemented each milestone in a fresh conversation, until all the sections were done. Sharing since all the tokens have already been spent on this.

The normalized unit-cake main theorem and its asymptotic corollary are proved:
for every positive number `n` of agents, one Robertson–Webb protocol returns a
complete envy-free allocation
using at most `2 * 32^n * n^7 * (n!)^2` queries. The construction assembles
Sections 2–5's `Divide`, `Dominate`, `Core`, `Repair`, and `Permute` protocols.
The explicit bound is `2^{O(n log n)}`.

Run `lake build` to check the project using the pinned Lean and mathlib versions.
See [the formalization guide](docs/formalization.md) for the paper-to-Lean theorem
map, modeling conventions, and verification instructions.
