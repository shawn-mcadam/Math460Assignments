# MATH 460/872 Assignment 3

This assignment is somewhat informal because categories are particularly difficult to formalize. You will use pen and paper to work directly with the definition of a category and you will use Lean to formalize (tractable) proofs of relevant results.


### Incomplete sketch of the assignment:

Define a monoid & symmetric monoid in Lean?
- Prove that a group has a monoidal structure (see MIL chapter 7)


##### Definition: category
A category is a set of objects 

We can define categories from graphs. Two such ways are Free and Preorder.

Every other category is in between these two. 

Consider $\mathbf{Set}$, $\mathbf{FinSet}$, and $\mathbf{Bij}$.


A monoid is ...

We can use the language of category theory to define a monoid: A monoid is a category with one object.

Define isomorphism.

A group is a monoid such that every morphism is an isomorphism.

Is $\mathbf{Bij}$ a group? Which group is it?



- Discrete category (all the morphisms are id)
- Topological category maybe depending on how they're used in CH7 of ACT. Include a $\epsilon-\delta$ proof that way?

Define small, locally small, and large categories informally
- Ask students if some of the above categories are small or large. Which of the large categories are locally "small"?
Recall that the Yoneda embedding lemma only applies to locally small categories. Informally, it states that we can study the set of functors from $\mathcal{C}\to\mathbf{Set}$ instead of directly studying $\mathcal{C}$ (presheaves are almost one such functor). (Yoneda applied to a group is called the Cayley theorem?)

Is a $\mathcal{V}$-category is a category?





Construct a morphism between categories
- 1 -> 2
- Can we show there's no morphism from preorder to free?

Define $\mathbf{Cat}$, the category of categories whose arrows are functors.

Have students draw 1-2 diagrams. Write an equation describing what it means for a diagram to commute.
- Informally provide the equations required for a given diagram to commute


Define a natural transformation
Natural transformation if a certain diagram commutes.
- Provide the equations

Include an example from the textbook

Construct the natural transformation between a group and its opposite $G^{\mathrm{op}}$
- https://en.wikipedia.org/wiki/Natural_transformation#Opposite_group



Question about a cartesian closed category + currying arrows in $A\times C$ + show something is cartesian closed (exercise 7.11)


Limits, pullback, pushout, presheaves (which are morphisms with more terminology), and sheaves (which are presheaves with some more properties) lead to topos. A topos is a category of sheaves. They are nice to work with because they possess many of the same properties as the category $\mathbf{Set}$. In particular, a topos
	1. has limits and colimits
	2. is cartesian closed
	3. has epi-mono factorizations (see definition 7.5 from textbook)
	This is enough properties to do logic with semantics (ie there are nice definitions of $\wedge,\vee,\neg,\implies,\exists,\forall$)

If we can show a category $\mathcal{C}$ is a topos then we've efficiently proven that $\mathcal{C}$ possesses all of the above properties. Furthermore, we can use logic operations to study more about $\mathcal{C}$.
