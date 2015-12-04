# OperationalSemanticsC11
An operational semantics for C11. [![Build Status](https://travis-ci.org/anlun/OperationalSemanticsC11.svg?branch=master)](https://travis-ci.org/anlun/OperationalSemanticsC11)

To run or compile the project for the first time you need to run `make link`.
It downloads and installs dependencies (`racket-pretty-printing-combinators` library),
compiles and installs the project. Futher you need to run `make setup` or just `make` to recompile it.
The project needs a version of DrRacket >= 6.2.1.

### Structure of the project:
- `core/`
  - The language family syntax description (`syntax.rkt`).
  - Syntax related reduction rules (`coreLang.rkt`).
  - Concrete languages definitions (`langs.rkt`).
  - The language state pretty printer (`pp.rkt`).
  - Language related utility functions (`coreUtils.rkt`, `syntax.rkt`).
  - Graph state representation related utility functions (`graphUtils.rkt`).
- `rules/`
  
  Sets of different sublanguage rules.
- `test/`
  
  Test terms and tests for different sublanguages and rules combinations.
