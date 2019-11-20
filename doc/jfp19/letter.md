We would like to thank the reviewers for their kind words and helpful
comments and suggestions. We have applied all the minor revisions they
requested and have expanded some sections to accomodate their requests.
We have also answered some questions we consider outside the scope of
this paper below in the "Clarifications" section of this cover letter.

We have highlighted the non-cosmetic changes with a bar of colour in
the margin. The colour of the bar corresponds to the reviewer who
motivated the change:

* blue  for reviewer 1
* red   for reviewer 2
* green for reviewer 3

# Major changes

* We have introduced a section 9.1 on relation transformers featuring
  `Kripkeᴿ` (formerly introduced in the Simulation section) and the
  pointwise lifting of a relation over environment and the relator
  lifting relations over d-shaped semantical `layers'.

* We have drastically reorganised the Simulation section, removed old
  terminology (such as 'synchronized') that reviewer 2 noticed, and
  introduced `bodyᴿ`.

# Clarifications

## Reviewer 1

> Later on in the conclusion you mention Kaiser, Schaëffer and Starks's remark
> that assuming functional extensionality, all traversals of ACMM are stable
> under renaming.
> Couldn't the extensionality requirement be dropped by considering a
> different representation of environments (...)

The problem lies somewhere else. The compatibility of semantics with renaming
ultimately amounts to a statement about two different evaluations of the same
term yielding the same value. If we have a renaming ρᵥ (ᵥ for var) and an
evaluation environment ρₛ (ₛ for semantics), the statement looks something
like: ((t [ρᵥ]) [ρₛ]) is equal to (t [ρₛ ∘ ρᵥ]).

This 'is equal' is the hard thing to deal with: subterms with extra bound
variables are interpreted as (Kripke) function spaces in the host language
and the only thing we can prove generically about them is that they take
equal values to equal results. So an intensional notion of equality will
simply not do.

We have expanded the remark in Section 9.2 to include this explanation.

> generic implementations of lifting and substitution in the more
> space-efficient fashion which does not carry a substitution everywhere
> but only a lifting index and does the de Bruijn arithmetic at the
> variable sites only.

Based on the ideas developped in ``Everybody's Got To Be Somewhere''
(McBride, 2018) and prompted by this remark, we were able to implement a
refactored version of semantics which does not retraverse its environment every
time it pushes it under a binder. This works by reifying the pattern
``weakening the existing environment and extending it with new values''
as a datastructure. When looking up a value in this ``environment'', we
get back a value together with a thinning obtained by composing all the
ones encountered on the way. We can then use th^V *once* before using the
var field of the Semantics to produce a computation.
You can see this alternative construction here:
https://github.com/gallais/generic-syntax/commit/97eb75906d04ec8fafbb45efb144d90fa05a6c09

This extension is too young and we have not yet proven it equivalent to
our usual notion of semantics so we should probably not include it in the
paper.

## Reviewer 2

> For the generic version of NbE in section 7.7, currently the
> positivity checker has to be disabled. However (as the paper also
> notes) this can destroy the soundness of Agda's theory. Thus I
> wonder whether it would be possible to provide a safe (but still
> generic) version of NbE by using either a Delay monad or define a
> suitable domain directly using domain theory.

Formalising enough domain theory to achieve this goal is outside the scope
of this paper. We have conducted experiments with an approach inspired by
step-indexed relations and tried to define a ℕ-indexed version of the domain
by recursion over the number of steps. This approach generated huge Agda
computations and we were not able to normalise even the most simple of toy
examples.


## Reviewer 3

> p3. This page states that the techniques are language-independent,
> requiring only inductive families, but it seems to me that the use of
> sized types is a key part of making the fixed point construction go
> through. Is that not the case?

Sized types are helping the termination checker see that our constructions
are justified by guaranteeing at the type level that the recursive call may
only be used on smaller terms.
This allows us to use higher-order function which introduce a level of
indirection between the recursive call being formed by partial application
and it actually being applied to a proper subterm.
But the use of sized types is not crucial: inlining and specialising said
higher-order functions would also allow the termination checker to realise
that all the recursive calls are justified (see for instance the dissertation
of Mendel-Gleason ``Types and verification for infinite state systems'' for
a similar approach to checking productivity by super-compilation).

The typical example is the definition of `map` for a rose tree. Using Haskell
syntax:

```haskell
data RTree a = Node a [RTree a]

-- map using List.map
map :: (a -> b) -> RTree a -> RTree b
map f (Node a rs) =
  Node (f a) (List.map (map f) rs)
                    -- ^ partially applied recursive call,
                    --   hard to see that it will only be used on subterms

-- map defined together with maps, the inlined and specialised version
-- of (List.map (map f)). All the recursive calls are performed on strict
-- subterms.
map  :: (a -> b) -> RTree a   -> RTree b
maps :: (a -> b) -> [RTree a] -> [RTree b]

map f (Node a rs) =
  Node (f a) (maps f rs)

maps f []       = []
maps f (r : rs) = map f r : maps f rs
```

All of these technical details are however outside the scope of this paper.

> In the related work on alternative approaches via code generation
> (section 10.4), it would be interesting to also compare to the ott
> tool for mechanized metatheory.

As far as we can tell from Ott's user manual, Ott only generates
inductive definitions (not guaranteeing terms are well scoped)
and some basic traversals such as computing the set of free variables
or implementing substitution. It does not seem possible to obtain
mechanized results about the metatheory of the language.

# Debated points

* We have added a paragraph explaining the programming style
  which led us to pick the same name for the arrow constructor
  and the constructor of the isArrow view.

* Similarly we have explained the design decision behind ─Env.

# Additional extensions:

* Cheney's ``Toward a general theory of names: binding and scope''

While addressing the remark by reviewer 3 inciting us to compare
and contrast Bach Poulsen et al.'s work with ours, we were reminded
of Cheney's ``Toward a general theory of names: binding and scope''
and added a discussion of the possible extensions this works suggests.

* Hatcliff and Danvy's ``A generic account of continuation-passing styles''

While reformulating the reference to our previous work that was done in
3rd person (due to ICFP double blind constraints) we expanded on the
CPS translation. The hope is that readers will get a clearer sense of
whether they want to look into it.
