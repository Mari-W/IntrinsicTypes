# AutoSubstAgda

Autosubst 2[^Autosubst2] in Agda[^Agda].[^1]

## Abstract
tbd.

## Project Goals

1. Proof of concept:
    1. Intrinsically scoped, extrinsically typed System F (kinda works)
    2. Intrinsically typed System F (working on this)
4. Make agda understand that the rewriting system is confluent (will be a pain)
3. Generalization to Kits
   (this might actually not be desirable due to tradeoff between additional complexity and code size) 
4. Framework:
    1. Generic universe of syntaxes with binding[^UniverseOfSyntaxesWithBinding]
       (boring)
    2. Kitty-like meta framework based on reflection[^Kitty]
       (cool™)

[^1]: hopefully maybe some day
[^Agda]: https://wiki.portal.chalmers.se/agda
[^Autosubst2]: https://www.ps.uni-saarland.de/extras/autosubst2/
[^Kits]: http://strictlypositive.org/Idiom.pdf
[^UniverseOfSyntaxesWithBinding]:https://arxiv.org/abs/2001.11001
[^Kitty]: https://github.com/m0rphism/kitty/
