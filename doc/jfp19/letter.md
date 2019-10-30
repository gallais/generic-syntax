We have highlighted the non-cosmetic changes with a bar of
colour in the margin. The colour of the bar corresponds to
the reviewer that motivated the change:

* blue  for reviewer 1
* red   for reviewer 2
* green for reviewer 3

# Clarifications

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

# Debatted points

* We have added a paragraph explaining the programming style
  which led us to pick the same name for the arrow constructor
  and the constructor of the isArrow view.


# Additional extensions:

* Cheney's ``Toward a general theory of names: binding and scope''

While addressing the remark by reviewer 3 inciting us to compare
and contrast Bach Poulsen et al.'s work with ours, we were reminded
of Cheney's ``Toward a general theory of names: binding and scope''
and added a discussion of the possible extensions this works suggests.

* Hatcliff and Danvy's ``A generic account of continuation-passing styles''

While reformulating the reference to our previous work that was done in
3rd person (due to ICFP double blind constraints) we expandend on the
CPS translation. The hope is that readers will get a clearer sense of
whether they want to look into it.
