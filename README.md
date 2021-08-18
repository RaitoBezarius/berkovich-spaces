# Towards Berkovich spaces formalization

This is an attempt to formalize Berkovich spaces in the Lean theorem prover.

So far, only Ostrowski theorems have been formalized:

- over rationals ;
- over polynomials (should be possible to extend it to K(X) with more work).

## Try this repository

You should have a recent Lean 3 setup with mathlib precompiled and you can just open the repository and browse the files, the entrypoint is `src/ostrowski.lean` showcasing the theorem over Q.

Nix can be used to setup the initial dependencies, then you should use `leanproject get-mathlib-cache` to get the cache.
