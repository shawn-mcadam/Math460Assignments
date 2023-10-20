# Math 460/872 Assignment 1
This entire assignment is contained within `act.lean`.

### Purpose
The purpose of this assignment is to
- Set up a Codespace
- Start Leanifying Seven Sketches in Compositionality: An Invitation to Applied Category Theory (ACT) 
- Get experience with structures

### Part 1
The first three questions in this assignment are exercises from _Mechanics of Proof_, an online book by H.R. MacBeth which you can access here: [Mechanics of Proof](https://hrmacbeth.github.io/math2001/index.html). Supply the proofs of the three examples at the beginning of `act.lean`.

### Part 2
The second part of `act.lean` is very incomplete. Currently, this file is a skeleton of ACT chapter 1. Find any place with a `TODO` or `sorry` and fill in the details.
You must
1. Set up a namespace
2. Show the DiscretePreorder is a preorder
3. Define the Prop `monotone` which takes a function as an input
4. Prove the identity over a preorder is monotone
5. Prove the composition of two monotone functions is monotone

### Recommended tactics
Students are allowed to solve these problems by any means; however, this is a list of very useful tactics for solving these problems:
- intro
- rw \[hypothesis\]
- calc
- apply
- apply?
Make liberal use of `apply?`
