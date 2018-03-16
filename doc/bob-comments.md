

Lines (3:34-3:38): This is pretty difficult to understand if one is
vaguely comfortable with Agda types. The 'I-Scoped' makes the types of
Var and Lam look ill-formed, and the sqbrackets look weird. Can these
things be signposted more clearly in the text?

GA - Not sure what to do extra here. The combinators and --Scoped are
defined above, the normalised version of the types is given.


# Section 5

Line (9:30): Is there an obvious reason why the CDMM universe as two
indexes, I and J, while this one has one? Could we simplify the CDMM
to just have one? (with a note that we are presenting a simplified
version of their definition)

GA - I adopted this type which Dagand used purely for type-tetris
reasons: it makes the implementation even more obvious. I'm okay
with downgrading it to I = J.

# Section 7

Line (16:1) (this section): Can this be done with fuel to avoid
turning off the positivity check (as in Bach Poulsen et al?)

Line (19:48): I was expecting a discussion of why the Semantics
framework can't express the unrolling function? Can we speculate on a
yet more generic framework that could?

GA - I can't remember why tbh. However it may be worth dedicating a
whole subsection to things that don't fit in the Sem framework.
E.g. talking about how Chapman's delayed big-step semantics can't be
handled (because it *restarts* evaluation when, after having evaluated
a function and its argument, it discovers that combining both forms a redex.

# Section 8

Line (21:45): Is this the first mention of POPLmark reloaded. Should
we boast about it more in the introduction? Is there a reference or
URL we can point to?

GA - It' also submitted to ICFP. Not much we can say.

# Section 9

Line (25:48): "oracle" => "oracles". Also, in this section are we just
restricting to type-theory based ones? I'm sure there are many more
than just these (Pouillard's one?, Nominal Isabelle).


Line (26:7): Kaiser et al are attempting to do System F, and the claim
here is that we are fully generic. However, is there any evidence that
we could do System F? It seems to me that the sorting system in the
universe in this paper is limited to simple types.

GA - I had a hard time following the paper even though I knew about
ACMM! I can't really comment

# Section 10

Line (27:27): Specifically, would this allow us to generically do
proofs of things like progress and preservation, confluence, etc.? Can
we automate ICFP paper generation?
