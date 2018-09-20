Generating Well-Typed Haskell Terms Using Neural Networks
=========================================================

### Setup

If you have [Stack](https://docs.haskellstack.org/en/stable/README/), you should be able to just do:

```
stack setup # If it is the first time running
stack build
```

### Execute

After building, run a command of the following form:

```
stack exec HasNN-exe -- TestModule.hs -e 10000 --load=TwentyThousand.nn --save=ThirtyThousand.nn
```

This will train for 10000 iterations (`-e` flag), starting by loading
the `TwentyThousand.nn` neural network and saving the result in `ThirtyThousand.nn`.
All three flags are optional with the defaults found in `src/Shakespeare`.

### Layout

The `src` directory contains most of the interesting files.

  - `PalkaGenerator` and `DumpGHCTerms` are adopted from Michal Palka's [Testing an Optimizing Compiler](http://www.cse.chalmers.se/~palka/testingcompiler/)
  - The `Tokenizer` module parses a Haskell source file into tokens.
  - The `Shakespeare` file contains the neural network currently developed.

The `.nn` files are neural networks trained with a different number of iterations. None of them really work yet.
