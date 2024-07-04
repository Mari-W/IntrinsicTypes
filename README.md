# AutoSubstAgda

## Abstract

AutoSubstAgda tries to reduce boilerplate code for reasoning about renamings and substitutions when mechanizing proofs about languages with variables and bindings in Agda[^Agda].

To tackle the problem of automatically deriving reasoning about renamings and substitutions we begin by defining parallel, multisorted renamings and substitutions. 
We then proceed to prove equality lemmas about their interaction that form a _confluent and _normalizing_ rewriting system by hand, similar to the laws formulated in Autosubst 2[^Autosubst2] that are based on the sigma calculus[^SigmaCalculus]. 
Furthermore, we embed these equalities as rewriting rules into Agda using `{-# REWRITE #-}`. 
We also mark all implementation as `abstract` such that the rewrite system stays normalizing and confluent, because the reductions of our function definitions should not interfere with the rewriting system.
Finally we build an abstraction layer to automatically derive everything for user defined syntaxes, either by building a generic universe or by using reflection.

## Project Goals

1. Proof of concept:
    1. Intrinsically scoped, extrinsically typed System F 
    2. Intrinsically typed System F
3. Generalization to Kits:
   Unify the handling of renamings and substitutions by using Kits[^Kits]
4. Framework:
    1. Generic universe of syntaxes with biding[^UniverseOfSyntaxesWithBinding]:
     ...
    2. Kitty-like meta framework based on reflection[^Kitty]:
     ...

## Questions

- Representation Independence: 
  Is it possible to formalize substitutions/renamings as functions as well and still use `REWRITE`?
- Relation to Autosubst 2:
  How does this approach differ from the one taken by Autosubst 2?
  Key points seem to be:
    - Deep embedding of the rewriting system into Agda's semantic instead of generating lemmas 
    - Either a generic universe of syntaxes or reflection based approach instead of plain code generation
    - Parallel substitution acting on multisorted syntax instead of vector substitutions

[^Agda]: https://wiki.portal.chalmers.se/agda
[^Autosubst2]: https://www.ps.uni-saarland.de/extras/autosubst2/
[^SigmaCalculus]: https://www.cambridge.org/core/journals/journal-of-functional-programming/article/explicit-substitutions/C1B1AFAE8F34C953C1B2DF3C2D4C2125
[^Kits]: http://strictlypositive.org/Idiom.pdf
[^UniverseOfSyntaxesWithBinding]:https://arxiv.org/abs/2001.11001
[^Kitty]: https://github.com/m0rphism/kitty/