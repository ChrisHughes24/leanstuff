# Algebraic closure roadmap

## Bundling homs
Ring homs should be bundled particulary in `polynomial.lean`, but also `adjoin_root` I don't use ideals anywhere in the construction.

## Directed colimits
This should be refactored to use bundled homs and the category theory library. Reid Barton told me he had a plan for this and was planning on doing it.

## Algebra homs
Get rid of all use of `algebra.comap` in statements of theorems and use the assumption that the appropriate maps commute instead. The `algebra` instance is sometimes only equal, but not definitionally equal to the one needed.

## Fix existing algebraic closure code
Once the above is all done, the existing algebraic closure code can be fixed. Only the code in the PR for the construction need be fixed, since I have a different plan for proving the map.
