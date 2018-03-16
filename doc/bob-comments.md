

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

Line (19:36): "which infinite list ought" => "the infinite list that
ought"

Line (19:38-42): should we mention that we are using copatterns here?

Line (19:48): I was expecting a discussion of why the Semantics
framework can't express the unrolling function? Can we speculate on a
yet more generic framework that could?

Line (20:7): I'd remove the first sentence of this paragraph -- this
point was already made above multiple times and isn't really talking
about the unfolding function.

# Section 8

Line (20:14): "their specific language" => "the untyped
lambda-calculus"

Lines (20:24-30): missing full stops at the ends of the bullet points.

Line (21:5-8): The text uses $\R^\C$ and $\R^\V$ (superscripts), but
the Agda code uses $\R\C$ and $\R\V$.

Line (21:18): Where are $\R\C$ and $\R\V$ bound? Should they be
parameters of Sim?

Line (21:45): Is this the first mention of POPLmark reloaded. Should
we boast about it more in the introduction? Is there a reference or
URL we can point to?

Line (22:9): "This Simulation" => "The Simulation"

Line (22:9): remove "of the kind" and insert "the" after the remaining
"of"

Line (22:13): add "for all syntaxes definable in our framework." at
the end of the sentence.

Line (22:21): remove "last but not least"

Line (22:26): mispelled "intrinisically"

Line (22:28): "shave off a lot of" => "remove"

Line (23:8): I think the boxes here are missing symbols?

Line (23:14): Put the reference to Section 6.1 in parens, and add the
word "Section".

Line (23:18): "dummy" => "placeholder"

Line (23:23): "lookup" => "look up"

Line (23:32): mispelled "algebra"

Line (23:34): "dummy" => "placeholder"

Line (24:30): Explicitly state that this is in the online materials?

Line (25:11): "As the reader can see the proof is trivial" => "The
proof is straightforward due to the simplicitly of this example"

# Section 9

Line (25:41): Reword to avoid looking like we've not managed to
improve on 9 year old work. Can we handle Hamana's extension?

Line (25:48): "oracle" => "oracles". Also, in this section are we just
restricting to type-theory based ones? I'm sure there are many more
than just these (Pouillard's one?, Nominal Isabelle).

Line (26:7): Kaiser et al are attempting to do System F, and the claim
here is that we are fully generic. However, is there any evidence that
we could do System F? It seems to me that the sorting system in the
universe in this paper is limited to simple types.

Line (26:21): "pattern synonym (Pickering et al. 2016) make working"
=> "pattern synonyms (Pickering et al. 2016) makes working"

Line (26:30): With respect to Erdi's work, what is new in this paper?

# Section 10

Line (26:38): I'd spell out ACMM here in case anyone skips forward to
the conclusion without reading the middle of the paper.

Line (26:43): "have managed to give" => "have given"

Line (27:13-27): Maybe make this a bullet list?

Line (27:15): *extremely pedant voice* "raises the question", not
"begs the question". (The NBE example begs the question, by being
circular).

Line (27:17): "the refinement of" => "refinements of"

Line (27:27): Specifically, would this allow us to generically do
proofs of things like progress and preservation, confluence, etc.? Can
we automate ICFP paper generation?








