# MATH 460/872 Assignment 3

This assignment is somewhat informal because categories are particularly difficult to formalize. You will use pen and paper to work directly with the definition of a category and you will use Lean to formalize (tractable) proofs of relevant results.

$~$

## Informal section:

A category $\mathcal{C}$ is a collection of objects and arrows with the following nice properties. This definition was taken from section 3.2 of ACT.
### Definition: category; objects; morphisms; identity; composite; $\mathcal{C}$; $\mathrm{Ob}(\mathcal{C})$; $\mathcal{C}(a,b)$
A category $\mathcal{C}$ satisfied the following.
1. There is a class of objects $\mathrm{Ob}(\mathcal{C})$, elements of which are called _objects_.
2. For every two objects $a,b\in\mathrm{Ob}(\mathcal{C})$, there is a class of _arrows or morphisms from a to b_ written $\mathcal{C}(a,b)$ called the _hom-set from a to b_.
3. For every object $a\in\mathrm{Ob}(\mathcal{C})$, there is an identity morphism $\mathrm{id}_a\in\mathcal{C}(a,a)$.
4. For every three object $c,d,e\in\mathrm{Ob}(\mathcal{C})$ and pair of morphisms $f\in\mathcal{C}(a,b)$,$g\in\mathcal{C}(b,c)$, there is a third morphism $g\circ f\in\mathcal{C}$.

Furthermore, categories must satisfy the following properties
1. _unitality_: for every morphism $f\in\mathcal{C}(a,b)$, composing with the identity of $a$ or $b$ does nothing. So, $\mathrm{id}_b \circ f = f$ and $f \circ \mathrm{id}_a = f$.
2. _associativity_: for any three morphisms $f\in\mathcal{C}(a,b),g\in\mathcal{C}(b,c),h\in\mathcal{C}(c,d)$, we have $(h\circ g)\circ f = h\circ (g\circ f)$.

Notes,
- Sometimes the hom-set $\mathcal{C}(a,b)$ is written as $\mathrm{Hom}_{\mathcal{C}}(a,b)$.
- $a\in\mathcal{C}$ means $a\in\mathrm{Ob}(\mathcal{C})$.
- It is convenient to denote morphism $f\in\mathcal{C}(a,b)$ as $f:a\to b$. We refer to $a$ as the _domain_ of $f$ and $b$ as the _codomain_.

We haven't specified much in the definition of a category. The names _objects_, _morphism_, _identity_, and _composite_ hints at how categories are typically used; however, the freedom in their definition makes categories highly adaptable.


$~$

This section explores how to construct a category from a graph. Two such methods are $\mathrm{Free} : (V,E)\to\mathcal{C}$ and $\mathrm{Preorder} : (V,E)\to\mathcal{C}$.
In both cases, the vertices $V$ become objects and the edges $E$ become morphisms. The two categories have a different number of morphisms. 

Key takeaways from this section are that:
- Any preorder can be regarded as a category and every category can be "crushed down" into a preorder.
- Both preorder and 


$~$

### Definition: $\mathbf{Set}$; $\mathbf{FinSet}$; $\mathbf{Bij}$
ACT defn $3.24$: $\mathbf{Set}$ is the category of sets whose morphisms (aka arrows) are functions.
- $\mathrm{Ob}(\mathbf{Set})$ is the class of all sets. So, saying $A\in\mathrm{Ob}(\mathbf{Set})$ is equivalent to saying $A$ is a set.
- For each $S,T\in\mathrm{Ob}(\mathbf{Set})$, the arrow $f\in\mathbf{Set}(S,T)$ is a function mapping $S$ to $T$ (ie $F:S\to T$).
- For each $S\in\mathrm{Ob}(\mathbf{Set})$, the identity morphism is the function $\mathrm{id}_S: S\to S$ such that $\mathrm{id}_S(s) = s$ for each $s\in S$.
- Given $f:S\to T$ and $g:T\to U$, their composition is $g\circ f : S\to U$.

Many categories are built from set. For example, $\mathbf{FinSet}$ the the category of finite sets. $\mathbf{Bij}$ is the category of sets whose morphisms are bijections (one-to-one/injective and onto/surjective functions).

$~$

#### Definition: monoid
ACT defn $2$:
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

Is a $\mathcal{V}$-category is necessarily a category?





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


Define a monoid & symmetric monoid in Lean?
- Prove that a group has a monoidal structure (see MIL chapter 7)
