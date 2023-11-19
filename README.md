# Automated verification from first principles

This repo is intended as a learning/teaching tool for automated reasoning
and verification based on wp reasoning. Specifically, the goal is to perform
basic wp verification of pre-and-post conditions without external solvers. To 
that end the minimal set of components are a DPLL(T) solver, an instantiation 
with uninterpreted functions, trigger based quantifier instantiation and 
WP-transformers for a test lanuage.

# Components
- [x] DPLL solver
- [ ] DPLL(T) extensions
- [ ] UF Theory
- [ ] Ematching Quantifier instantiation
- [ ] Syntax/Semantics for a test lanuage
- [ ] WP-transformers

Future plans
* CDCL(T) solving
* Implicit dynamic frames
* MBQI
* Additional theories
