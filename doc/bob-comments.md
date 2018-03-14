# Abstract

Almost every programming language's syntax includes a notion of bound
variable, and the accompanying notions of $\alpha$-equivalence,
capture avoiding substitution, typing contexts, runtime environments,
and so on. In the past, implementing and reasoning about programming
languages has required careful handling to maintain the correct
behaviour of bound variables. Modern programming languages now include
features that enable constraints like scope safety to be expressed in
types. Nevertheless, the programmer is still forced to write the same
boilerplate over again for each new implementation of a scope safe
operation (e.g., renaming, substitution, CPS transformation, printing,
etc.), and then again for correctness proofs.

In this paper, we present an expressive universe of syntaxes with
binding and demonstrate how to (1) implement scope safe traversals
once and for all by generic programming; and (2) how to derive
properties of these traversals by generic proving. Our universe
description, generic traversals and proofs, and our examples have all
been formalised in Agda and are available in the accompanying
material.

* CCS Concepts, and the Key words are wrong

# Introduction

Line (1:30): Remove "software"?

Line (1:33): "for their deep embedding" => "for their deeply embedded
syntax". Is it appropriate to include "deep embedding" here? It is a
slightly technical phrase that has prompted some confusion amongst the
ICFP community in the past. Perhaps just "for representing their
syntax".

Line (1:33): "they" => "programmers" (more concrete)

Line (1:35): Remove the semicolon and start a new sentence. Swap the words
"only" and "enforcing".

Line (1:37): "primers on ... variant as well as ..." =>
             "a primer on scope safe and type and scope safe terms, as well as ...

Lines (1:41-2:4): Put in forward references to the places where we
substantiate these claims. These are the main contributions of the
paper, and it is good to point directly to where the reader can find
them.

# Section 2

Line (2:7): Remove the word "strict"? what does it mean in this
context? Bigger point: what about variables in open terms? They
haven't been introduced in by a binder. Maybe replace this paragraph
with: "Scope safe terms follow the discipline that every variable is
either bound by some binder or is explicitly accounted for in a
context. A scope safe programming language is one in which all valid
terms are scope safe."

Lines (2:10-2:17): I worry that this paragraph jumps into category
theoretic language too quickly. Can we say "inductive type" instead of
"fixpoint of an endofunctor"? Maybe also use $\Set \to \Set$ instead
of the exponentiation notation?

Line (2:15): Remove the word "Conversely"

Line (2:22): Remove "Last but not least"

Lines (2:26-2:31): The phrases "The functorial action" and "the
monadic action" prompt me to ask "where did they come from?". I think
we should instead say: "Since 'Lam' is a endofunction on Set, it makes
sense to ask whether it is also a functor and a monad. Indeed it is,
as Altenkirch and Reus have shown. The functorial action corresponds
to renaming, the monadic 'return' corresponds to the use of variables,
and the monadic 'join' corresponds to substitution. The functor and
monad laws correspond to well known properties from the equational
theories of renaming and subsitution. We will revisit these properties
below in Section XXX."

Lines (2:26-2:29): "mapping" has two 'p's.

Line (2:35): "what ... monads" => "using Altenkirch, Chapman, and
Uustalu's relative monads (2010;2014)".

Line (2:36): "objects are 'List I'" => "objects are inhabitants of
'List I'" (or "objects are lists of 'I's"). The text doesn't
explicitly say what 'I' is before using it, and since we are
*defining* a 'J', it is not immediately obvious that 'I' is a user
selected parameter. Maybe rearrange the paragraph to mention what 'I'
is at the start? Also, should 'List I' be blue?

Line (2:37): Remove the word "straightforwardly"; maybe replace with
"is intended to represent".

Line (3:1): Our results are language independent if your language is
dependent! (seriously: maybe mention Coq, Lean, Idris as examples)

Line (3:4): I'm not sure about the word "weaponise". Maybe
"exploit". Also, could "threaded" be replaced with "passed unchanged",
and "adjusted" with "extended"? And "In order" at the start of the
sentence could be removed.

Line (3:6/7): There should be a reference to Fig. 2 somewhere, so the
reader knows where to look.

Line (3:16): "one" => "combinator". Better: name it explicitly. Also,
remove the word "simply".

Line (3:17): The '[_]' combinator has already been mentioned at the
end of the previous paragraph.

Lines (3:19-3:25): The 'I's here are just "any old set", right? They
aren't necessarily related to the 'I' in 'I-scoped'? In fact, the 'I's
in this type will often be 'List I'? Maybe use another letter?

Lines (3:34-3:38): This is pretty difficult to understand if one is
vaguely comfortable with Agda types. The 'I-Scoped' makes the types of
Var and Lam look ill-formed, and the sqbrackets look weird. Can these
things be signposted more clearly in the text?

Line (3:42): "corresponds" => "represents"

Line (3:45): "Both of their types" => "Both of the constructors'
types".

Line (3:48): This doesn't look like normal Agda syntax. 'Var' seems to
have been curried, but the 'I-Scoped' definition isn't.

# Section 3

Line (4:6): "This type and scope safe deep embedding of the simply
typed $\lambda$-calculus ..." => "The scope and type safe
representation described in the previous section ..."

Line (4:7): replace "she is" with "they are" (and later on)

Line (4:8): "wants and needs" => "will naturally want to"

Line (4:9): remove "perhaps"

Line (4:9): remove "And" at the start of the sentence.

Line (4:10): "is" => "are"; and "in the terms' indices" => "statically"

Line (4:11): "type of" => "types of"

Lines (4:14-18): These definitions contain a lot of unexplained stuff:
environments are explained in the next para, so OK. But what are [[V]]
and 'extend'. Further down the page they are referred to, but not
explained. Is it possible to fit in a quick explanation of what they
do it each case?

Line (4:22): "We wrote" => "We have written"

Line (4:24): mispelled "environments"

Line (4:25): "the host language's" => "Agda's"

Lines (4:22-4:24): Maybe replace this paragraph with: "Both renaming
and substitution are defined in terms of \emph{environments} $(\Gamma
-Env) \V \Delta$ that describe how to associate a value (variables for
renaming, terms for substitution) well scoped and typed in $\Delta$ to every
entry in $\Gamma$. Environments are defined as the following record
structure (using a record helps Agda's type inference reconstruct the
embedded langauge's types for us):"

Line (4:33): Replace sentence with "The definitions of renaming and
substitution have very similar structure." (more direct; shorter)

Line (4:34): What does "function specific" mean here? That [[V]] and
'extend' are special to 'ren' and 'sub' separately? Wouldn't it be
better to add subscripts to distinguish them?

Line (4:37): remove "in dependently typed programming"; and remove
"precisely".

Line (4:40): "Unpublished": is this referring to my blog post, or to
some other unpublished results. Who by? I think there should be a
forward reference to the section where the type checking is done in
the new framework.

Line (4:42): Is it possible to put a short description of what each of
these things is, to help the reader?. E.g., "Thinings, a
representation of renamings; Thinnables, which are types that permit
renaming; and the $\Box$ functor, which freely adds Thinnability to
any indexed type."

Line (5:4): "we do not use such instances". Maybe add "However, such
extra flexibility will not get in our way, and permits a
representation as a function space which grants us the monoid laws
``for free'' as per Jeffery's observation (2011)."

Line (5:6): "combinator". It was a "functor" above.

Line (5:6): "It is akin too ... domain $D$". Maybe replace with "This
is accomplished by abstracting over all possible thinnings from the
current scope, akin to an S4-style necessity modality." I'm not sure
that mentioning Kripke-style quantification helps here. The fact that
it is called 'Box' signals a relationship to modal logic / possible
world semantics anyway.

Line (5:9): Remove "Last but not least". Start the sentence with "The
functor Box is a...". Perhaps also mention that these are the axioms
of S4 modal logic.

Line (5:11): "ot" => "to"

Line (5:13): is there a justification for why the coalgebras in
Thinnables aren't required to be comonad-algebras? We've just stated
that Box is a comonad, after all.

Line (5:14): Remove the word "Unsurprisingly"

Line (5:27): Perhaps remind the reader that this bit is recapitulating
ACMM.

Line (5:29): replace "various semantics" => "a choice of useful scope
safe traversals". Also: mismatched quote symbols around 'host language'

Line (5:29): Move last sentence to the next paragraph and replace
with: "Semantics are defined in terms of a choice of values $\V$ and
computations $\C$. Realisation of a semantics will produce a
computation in $\C$ for every term whose variables are assigned values
in $\V$."

Line (5:36): "not particularly interesting". This is a bit dismissive:
say instead "The semantical counterpart of application is an operation
that takes a representation of a function and a representation of an
argument and produces a representation of the result." Better to be
concrete and explicit.

Lines (6:12-13): Remove the "can"s. Also, it would help the reader to
know that 'pack' is the constructor for environments (it isn't obvious
from the name).

Line (6:29): "One of the main driving force". What does this mean?
Maybe replace with "We define a function 'fresh' that generates new
concrete names using a State monad.".

Lines (6:32-26): the way the indentation has laid things out here
makes it look like 'fresh' is part of the definition of 'Wrap'. Can
they can lined up to have the same left justification?

Line (6:40): "The wrapper 'Wrap' is trivially..." Better: "The wrapper
'Wrap' does not depend on the scope $\Gamma$, so it is automatically
as Thinnable functor."

Line (6:41): "application node". We haven't been calling them 'nodes'
before this. Maybe just "application".

Line (6:42): "string representation of the function" => "string
representation of the term in function position".

Line (7:15): I think it should be made clearer earlier on in this
section that it is a recapitulation of ACMM.

Lines (7:19-23): I think this paragraph is not very
understandable. What do you mean by "constraint"? The fact that \V
must be Thinnable, or the whole thing? Maybe this paragraph could be
shortened to: "The main contribution of this paper is the
generalisation of 'Sem' from the 'Lam' datatype to any user-defined
datatype with binding. Before we do this, we need to look at
descriptions for datatypes without binding. In Section 5, we will
unify datatype genericity with binding."

# Section 4

Line (7:32): "this universe" ==> "CDMM's universe"? (putting the
acronym in the previous para)

Line (7:35): "to stop, ..." => "to stop with a particular index
value."

Line (7:36): "They essentially give rise ..." => "Interpretaton of
descriptions gives rise to right nested tuples terminated by equality
constraints."

Line (7:47): "she is" => "they are"

Line (7:47): I'd just remove the second part of this sentence ", using
.. expressivity." And add "The List typed is unindexed, we represent
the lack of an index with the unit type $\top$." (concrete example
better than generalities)

Line (8:13): Replace the sentence with: "Indexes can be used to
enforce invariants. For example, the type $Vec A n$ of length-indexed
lists."

Line (8:27): "Now that ... program over them" ==> "The payoff for
encoding our datatypes as descriptions is that we can define generic
programs for whole classes of data types."

Line (8:44): "Here". In this layout, the 'here' is a bit lost because
the figure has been forced onto the next page. Maybe refer to the
Figure number?

Lines (8:44-9:12): THis description of sizes takes up quite a bit of
space. Can we shorten it to mentioning that we need Sizes to get Agda
to accept this definition, but that describing it in detail would be a
distraction.

Line (9:13): What does "This" refer to? The last thing that was
mentioned was sizes. Maybe replace this paragraph with: "The CDMM
approach therefore allows us to generically define iteration and
induction principles for all data types that can be described. This
are exactly the features we desire for a universe of data types with
binding, so in the next section we will see how to extend DCMM's
approach to include binding." (don't bother mentioning the infinite
branching, I think it is a distraction here).

# Section 5

Line (9:24): insert a comma before "except"

Line (9:24): Is there a reason that 'Set' is bolded (the "category"
Set)? Why not use the Agda blue?

Line (9:25): Maybe refer back to the Var and Lam datatypes defined "by
hand" in Section 2.1?

Line (9:25): "Descriptions ..." I think this sentence would be better
worded to highlight the changes with respect to the CDMM universe
described in the previous section. Perhaps: "We now think of the index
type 'I' as the sorts used to distinguish terms in our embedded
language. The $\`\sigma$ and $\`\Box$ constructors are as in the CDMM
Desc type, and are used to represent data and index constraints
respectively. The $`X$ constructor is now augmented with an addtional
'List I' argument that describes the new binders that are brought into
scope at this recursive position."

Line (9:30): Is there an obvious reason why the CDMM universe as two
indexes, I and J, while this one has one? Could we simplify the CDMM
to just have one? (with a note that we are presenting a simplified
version of their definition)

Line (9:38): "not quite" vs "more general" if it isn't quite a
functor, then how can it be more general? (I'm only commenting on the
apparent contradiction in the text)

Lines (9:38-44): I found this paragraph quite difficult to read
because the definition of the meaning function had been pushed to the
next page.

Line (9:39): On a first read, this clause just seems to suddenly end
with a jumble of greek letters. Perhaps giving the type of X in the
running text?

Line (9:46): Remove "simply"

Line (10:39): "We can then define" ==> "For convenience, we define"

Line (10:41): "seemlessly" => "seamlessly"

Line (10:46): remove "her"

Line (10:47): If you change the UTLC example to use a custom datatype
for constructor names (next point), then change this sentence to:
"This is now four times that we have given datatypes with two
constructors.".

Line (11:1): Why not define a type `UTLC of UTLC constructors as you
did for STLC? It would be much easier to read than using Bool.

Line (11:41): The 'All' type is not defined anywhere.

Line (11:46): Would "combinators" be better than "results"?

# Section 6

Line (12:3): I think it would be better to start this sentence with:
"Based on the Sem type we defined for the specific example of the
untyped $\lambda$-calculus in Section 3,"

Lines (12:7-12): Maybe mention the corresponding field name for each
item? Also, is "constraint" the right word? Maybe "data", as in "These
two families must come equipped with the following data: "?

Line (12:10): Remove "Last but not least".

Line (12:10): "where" => "whose"

Line (12:11): I think the "Computations or Kripke functional spaces"
is confusing because we haven't yet seen the Kripke type. Maybe
replace with "replaced with Computations (possible under some binders,
represented semantically by the Krike type defined below), into
Computations."

Line (13:3): "We can then" => "We can now"

Line (13:6): Maybe add "; turning syntactic binders into semantic
binders."

Line (13:13): I'd change this sentence to "The proof of $sem$ is
straightforward now that we have clearly identified the problem
structure and the constraints we need to enforce."

Line (13:15): Remove "simply"

Line (13:16): "proper node" => "non variable constructor"

Line (13:28): insert "a auxillary function" after "thanks to".

Line (13:39): remove "trivially"

Line (13:42): should refer back to the ACMM definition of renaming,
which has the same structure.

Line (13:43): "two first" => "first two"

Line (13:45): remove "simply"

Line (13:46): would "placeholder" be better than "dummy" here? (and
below too)

Line (14:11): Should mention explicitly that vl^Var and vl^Tm are
proofs of VarLike for Vars and Tms respectively.

Line (14:32): "very easily prove" => "it is almost immediate that"

Line (14:35): Something funny's going on with the type signature of
reify: first arrow has nothing before it.

# Section 7

Line (14:43): "Other Generic Programs" => "A Catalogue of Generic
Programs for Syntax with Binding" (sounds more impressive)

Line (14:44): "languages" => "language"

Line (14:47): "we have already seen" => "we defined"

Line (15:3): "herself" => "themselves"

Line (15:17): "she" => "they"

Line (15:23): "both are" => "are both"

Line (15:23): "that" => "the"

Line (16:1) (this section): Can this be done with fuel to avoid
turning off the positivity check (as in Bach Poulsen et al?)

Line (16:34): remove "she may want to define."

Line (17:20): "Bob Atkey" => "Robert Atkey" (or just "Atkey")

Line (18:35): I could see how this claim ("in about a dozen lines of
code, we have..") might not impress a reviewer. The direct
implementation wouldn't be any longer would it? The point of this
example isn't that this was difficult or boring to do before, it is
that the Semantics framework is expressive enough to include it.

Line (19:32): "one thing still out of our reach with the current tools
we have" => "one thing still out of reach with our current tools"

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








