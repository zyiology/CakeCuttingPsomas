# AI Agent Guide

This file contains AI-specific guidance only. Human-facing documentation
is kept in the documents linked below.

- README.md
- docs/

Refer to appropriate documentation as required.

## AI-only rules

- When asked to plan work, create a detailed implementation plan and wait for user review before making code changes.
- After implementing a plan and ensuring it's correct, make a git commit of the changes for version tracking purposes.
- If requirements are unclear or missing, ask targeted questions before making assumptions.
- Apply independent software engineering judgement and optimize for long-term code quality. If a request conflicts with good software engineering principles (clarity, maintainability, correctness, performance, security), push back respectfully, explain the tradeoffs, and recommend a better approach. 
- Python tooling is managed with `uv`. Run Python, scripts, and project tools through `uv run`.
- Documentation should be concise, to orient users and developers to the project efficiently. README.md should be meant for a high-level overview of the project, while details for developers is kept in `docs/`.
- Follow the paper's definitions, algorithms, and proof structure closely.
- Cite the corresponding paper result in each major theorem's docstring.
- Never strengthen assumptions or weaken conclusions merely to obtain a proof.
- Search Mathlib and existing project code before introducing definitions.
