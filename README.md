Generating Well-Typed Haskell Terms Using Neural Networks
=========================================================

### Setup

If you have [Stack](https://docs.haskellstack.org/en/stable/README/), you should be able to just do:

```
stack setup # If it is the first time running
stack build
```

### Layout

The `src` directory contains most of the interesting files.

  - `PalkaGenerator` and `DumpGHCTerms` are adopted from Michal Palka's [Testing an Optimizing Compiler](http://www.cse.chalmers.se/~palka/testingcompiler/)
  - The `Tokenizer` module parses a Haskell source file into tokens.
  - The `Shakespeare` file contains the neural network currently developed.

The `.nn` files are neural networks trained with a different number of iterations. None of them really work yet.
