

Lines (3:34-3:38): This is pretty difficult to understand if one is
vaguely comfortable with Agda types. The 'I-Scoped' makes the types of
Var and Lam look ill-formed, and the sqbrackets look weird. Can these
things be signposted more clearly in the text?

# Section 5

Line (9:30): Is there an obvious reason why the CDMM universe as two
indexes, I and J, while this one has one? Could we simplify the CDMM
to just have one? (with a note that we are presenting a simplified
version of their definition)

# Section 7

Line (16:1) (this section): Can this be done with fuel to avoid
turning off the positivity check (as in Bach Poulsen et al?)

Line (19:48): I was expecting a discussion of why the Semantics
framework can't express the unrolling function? Can we speculate on a
yet more generic framework that could?

Line (20:7): I'd remove the first sentence of this paragraph -- this
point was already made above multiple times and isn't really talking
about the unfolding function.

# Section 8

Line (21:5-8): The text uses $\R^\C$ and $\R^\V$ (superscripts), but
the Agda code uses $\R\C$ and $\R\V$.

Line (21:45): Is this the first mention of POPLmark reloaded. Should
we boast about it more in the introduction? Is there a reference or
URL we can point to?

# Section 9

Line (25:48): "oracle" => "oracles". Also, in this section are we just
restricting to type-theory based ones? I'm sure there are many more
than just these (Pouillard's one?, Nominal Isabelle).

Line (26:7): Kaiser et al are attempting to do System F, and the claim
here is that we are fully generic. However, is there any evidence that
we could do System F? It seems to me that the sorting system in the
universe in this paper is limited to simple types.

# Section 10


Line (27:27): Specifically, would this allow us to generically do
proofs of things like progress and preservation, confluence, etc.? Can
we automate ICFP paper generation?








