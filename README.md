# Gray code in Lean

![Build/Proof Check](https://github.com/josephmckinsey/lean-graycode/actions/workflows/lean_action_ci.yml/badge.svg) [![Docs/Blueprint](https://github.com/josephmckinsey/lean-graycode/actions/workflows/blueprint.yml/badge.svg)](https://josephmckinsey.github.io/lean-graycode/)

[Homepage](https://josephmckinsey.github.io/lean-graycode/).

Formalization of [Gray code](https://en.wikipedia.org/wiki/Gray_code).

* Lots of bitwise lemmas about `^^^` and power of twos in $\mathbb{N}$.
* Definitions and theorems for Gray code sequences.
    * `list_gray_code`, `recursive_gray_code`, `direct_gray_code`, `recursive_inverse`, `direct_inverse`.

## Not formalized

* Linear algebraic characterization via $\mathbb{Z}_2$ vector spaces and XOR homomorphisms.
