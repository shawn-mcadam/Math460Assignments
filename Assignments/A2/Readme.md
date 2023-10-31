# MATH 460/872 Assignment 2

### Part 1
The file `a2.lean` contains various examples and theorems marked with `sorry` and TODO. Many of these exercises came from Glipse of Lean, some from Math in Lean. You will be filling in these proofs to get experience with
- the $\forall$ and $\exists$ quantifiers
- conjunctions and disjunctions (`\and` and `\or`)
- more of Lean's tactics (`constructor`)
- negations
- proofs by contradiction/contrapositive in Lean
This file concludes with a proof that for every function `f : A \to B` `image f` and `preimage f` form a Galois connection between the power set of A and the power set of B, ordered by the `\subset` relation.

### Part 2
Leanify any result of your choice from the first two chapters of the textbook. To do so, you must
1. Make a codespace from the ACT github TODO
2. Edit the file `act.lean`
3. In the terminal you will execute the following commands: `git pull`, `git add act.lean`, `git commit -m "my message here"`, `git push`
4. Then you will make a push request (PR) on the github browser. Dr. Dutchyn and many of your classmates will help you with these last steps.
5. The repo maintainers will resolve any possible conflicts and merge your PR. If two students leanify the same result, then the best proof will be used. Please don't do this intentionally. The goal is quantity, not quality (A messy correct proof is still correct).


### Additional comments:
It's always worth trying to use `apply?`, `ring`, `simp`, `rfl` whenever possible.

You can apply the tactics `unfold` and `simp` to a specific hypothesis with `at`.


### Recommended tactics
##### Useful tactics from each previous assignment:
- intro
- rw \[hypothesis\]
- calc
- rfl
- apply
- apply?
##### New useful tactics:
- unfold
- simp
- constructor
- rintro
- use
- intro
- have
- contradiction



If you want more practice before/after tackling these problems, please look through `GlimpseOfLean/`.
