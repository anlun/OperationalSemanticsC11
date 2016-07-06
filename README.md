# OperationalSemanticsC11
An operational semantics for the C/C++11 memory model.

### Installation
To run or compile the project for the first time you need to run
```
make link
```
It downloads and installs dependencies (`racket-pretty-printing-combinators` and `graph` libraries),
compiles and installs the project.
Futher you need to run
```
make setup
```
or just `make` to recompile it.
The project needs a version of Racket >= 6.4.

### How to write and execute own examples

You need to define a term. For this purpose you should write

```racket
(define myTerm
    @prog{TERM_BODY
          })
```

Consider the following term:

```racket
@prog{x_rel := 0;
      y_rel := 0;
      spw
      {{{ x_rel := 1;
          r1 := y_acq;
          ret r1
      ||| y_rel := 1;
          r2 := x_acq;
          ret r2 }}} }
```

More or less, it corresponds to the following program in
[cppmem](http://www.cl.cam.ac.uk/~pes20/cpp/) (\cite{Batty-al:POPL11}) syntax:

```c
atomic_int x, y;
int r1, r2;
x.store(0, mo_release);
y.store(0, mo_release);
{{{ { x.store(1, mo_release);
      r1 = y.load (mo_acquire); }
||| { y.store(1, mo_release);
      r2 = x.load (mo_acquire); }
}}}
```

Or in \cite{Vafeiadis-Narayan:OOPSLA13} syntax:

```
    let x = alloc() in
    let y = alloc() in
       [x]_rel = 0;
       [y]_rel = 0;
[x]_rel = 1 || [y]_rel = 1
    [y]_acq ||     [x]_acq
```

In our language there are two types of identifiers, which can be used
at the left hand side of an assignment --- locations and \valueName.
\valueName identifiers start with `r` symbol, location identifiers don't
start with `r`.
One doesn't need to declare locations, the first
write to a variable with appropriate name creates a location in the
program state.

Spawn construction represents starting two subthreads command.
```
spw {{{ THREAD_0_BODY
    ||| THREAD_1_BODY
    }}}
```

In the runtime subthreads are represented by `par` construction:
```
par {{{ THREAD_0_BODY
    ||| THREAD_1_BODY
    }}}
```


More examples you can find in [test/testTerms.rkt](test/testTerms.rkt).

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

