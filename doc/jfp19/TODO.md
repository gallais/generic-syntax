# James McKinna's remarks (with gallais' spin on them)

* [ ] The text uses copatterns to define an η-expansion of
  'pack s', but it is this later which is used in running text to
  describe the term. Can we reconcile this copattern vs. constructor
  terminology somehow?

* [X] Add ticked pattern synonyms for list and define foldr using
  them on page 13

* [X] Use a pattern-matching let in the definition of annotate
  instead of proj1

* [ ] norm^LC should use a locally defined `fire` function in the
  `(APP' (LAM f) t)`. Introducing this `fire` is a great opportunity
  to: - show its type
      - explain why `extract` and the *singleton* environment `ε • t`
        are used.

* [X] add `Rel`'s definition and introduce `packᴿ λ _ → refl` as `reflᴿ`.
  by analogy with other instances of 'pack var', 'pack id', ... ie
  'pack (Semantics.var S)' for some Semantics S, should we name this object,
  as 'the identity Relator' or some such?

* [X] Check Pierce and Turner's 'Local type Inference' (is cut explicitly considered?)

It is not, because substitution is taken as folded into the (very
baroque) ML(F-sub)-style instantiation rules for polytypes, and the
application rule; in inference mode, all of this is hidden in the
constraint solving algorithm. *All* term constructors have an infer-
and check-mode rule, so it is evident that they hadn't quite grokked
the proof-theoretic apsects of bidirectionality at that point. Pierce,
however, notes that bidirectional approaches are/were 'folklore', and
indeed that John Reynolds had introduced him to the main idea already
in 1988 (!).

* [X] Check Pfenning/Lovas, Pfenning/Dunfield, and Zeilberger (taken from
  Pfenning ICFP 2007) for potential cut-related comments.

I find substitution/cut both in Pfenning/Dunfield, "Tridirectional..."
(where the extra 'direction' is to account for the intersection/union
structure on top of mere subtyping), and in Pfenning/Lovas, but not
obviously also in Zeilberger (and while this latter's citation of
Lengrand/Dyckhoff might yield something, I see no point in pursuing
it).

Craig cites Pfenning's 15-312 lecture notes, "Foundations of
Programming Languages" (2004) in his forthcoming PhD thesis. I've
added that to the bib.

# Review 1 main questions / comments


* [X] You note in section 3.1 that renaming and substitution can be
  generically derived for all your syntaxes, relying on the notion of
  Thinability and VarLike values. To mechanize this, you choose to
  profit from the strict monoidal structure of arrow types to define the
  Thinning notion. A similar choice is made in the sigma-calculus
  presentation of Shaëffer et al (ITP 2015), where renamings are `nat ->
  nat` functions and substitutions `nat -> term` functions and one needs
  to show extensionality properties of functions using them. Later on in
  the conclusion you mention Kaiser, Schaëffer and Starks's remark that
  assuming functional extensionality, all traversals of ACMM are stable
  under renaming. Couldn't the extensionality requirement be dropped by
  considering a different representation of environments etc... using
  finite support functions (represented as finite tuples?). Especially
  in the case considered in this article, as all variables are
  well-scoped (_-Scoped), there must be a finite number of free variables
  in any situation. Of course one could also rely on an OTT/HoTT-like
  theory with functional extensionality built-in and not bother with this.
  Maybe the point you make is also about higher-order functions?

* [X] Suspended substitutions are hard, but I'm missing the other direction:
  generic implementations of lifting and substitution in the more
  space-efficient fashion which does not carry a substitution everywhere
  but only a lifting index and does the de Bruijn arithmetic at the
  variable sites only. It is easy to implement on untyped syntax, but it
  seems to me that the VarLike requirements prevent it in the general
  framework you present (of course, if it doesn't prevent it, I would be
  glad to know how to do it). As I understand it, the way semantics are
  defined, an application of renaming will switch between PHOAS-like
  (Kripke) and concrete (interpretation of a description) presentations
  of the term. IIUC, in the printing example, `reify` takes a Kripke
  function built from an existing concrete term, and applies it to built
  a new concrete term by combining it with the action of fresh, hence
  producing fresh names for the bound variables, already knowing about
  the names of the free variables computed with `(base vl^MName)`.  I'm
  curious what the computational content of these manipulations is and
  if the back-and-forth of going through Kripke function spaces is
  efficient or can be optimized? How would the renaming function you get
  through Semantics compare with a straightforward recursive
  implementation applying a lifting to the current renaming at each
  binder and with a function accumulating the lifting index (or types)
  and applying it in one go at the var leaves only (if that is indeed
  definable).

reify the th^Env calls into a datastructure using the diamond monad

* [ ] The obvious question that is not directly answered in future work
  is: would this lift to a dependently-typed language easily? The closure
  under products issue is the first obstacle I guess, and it could use
  an explanatory example. Probably this also links to the unrestricted
  variable sorting issue.

# Review 1 "presentation" comments

* [X] I guess you want figure 32 to appear on page 19, not 20.

solved by expanded paragraph after definition of VarLike.

* [X] p21. "where assigned"

removed.

* [X] p21. "the two first" -> "the first two"?

* [X] p22. The definition of `base` is missing.

(added on page 19 with VarLike).

* [X] p38. congruence rule for c -> s.

* [X] generic generic

# Review 2 "opportunities for improvement

* [ ] Since the 'variable' feature of Agda is quite new and the paper
      makes heavy use of it, perhaps it would help to add a short
      explanation of which variable declarations are used (e.g. "We use σ
      for variables of type Type and Γ for variables of type List Type").

* [X] For the scope checker in section 7.2, the error messages provide
      additional information as to what went wrong, but this is not the
      case for the typechecker in section 7.3 or the elaborator in section
      7.4. Is there a particular reason for using Maybe instead of a more
      informative Either here?

* [ ] Since the paper is quite long, it would help the reader to provide
      pointers to where concepts are defined, especially when it is more
      than one section ago since they were used. For example, 'case' from
      section 5 is used in the definition of UnLet in section 7.5, and
      'closed' from section 6.2 is used in 7.4.

Dealt with this one case. Need an additional reading of the **whole**
paper to detect all occurences of similar problems.

* [X] In the definition of elaboration in section 7.4, the letter Γ is
      used both for a List of modes and for a Typing. Although both are
      similar, it would be less confusing if they would use a different
      symbol.

Is this even true? We are using ms for lists of modes and Γ for typings!

* [X] It feels a bit silly to refer to your own 2017 paper in 3rd person.

ICFP double blind precautions. Took the opportunity to expand on the
Moggi's ML.

* [X] In Figure 48, I didn't find where 'Elaborate' is defined. If it is
      omitted from the paper intentionally, it would help to give at least
      its type signature.

* [X] For the generic version of NbE in section 7.7, currently the
      positivity checker has to be disabled. However (as the paper also
      notes) this can destroy the soundness of Agda's theory. Thus I
      wonder whether it would be possible to provide a safe (but still
      generic) version of NbE by using either a Delay monad or define a
      suitable domain directly using domain theory.

* [X] Currently the paper requires some knowledge of Agda's standard
      library to understand completely. For example, I had to look up the
      definition of Rel and rel which are used in section 9.1. It would
      improve the paper if it either explained these concepts or at least
      referred to the modules of the standard library where they are
      defined.

Not actually stdlib but good point: we should explain that just like we
need \_--Env, we also need Rel
Explained All too

* [X] I did not understand some of the terminology used in section 9.1,
      e.g. what does it mean for two objects to be 'synchronized'? And
      what does it mean for two environments to be 'extensionally equal'?

* [X] The POPLMark challenge is referenced on page 42, but it is mentioned
      already two pages earlier.

* [X] The sentence in section 10.3 ending with "... to go further in
      developing machine-checked such implementations and proofs" looks
      weird, maybe it's better to reword it in some other way?

* [ ] In the related work on alternative approaches via code generation
      (section 10.4), it would be interesting to also compare to the ott
      tool for mechanized metatheory.

* [X] There's a typo in section 11: the period at the sentence ending with
      "acting on all of them" is missing.

* [X] The usage of the word "preliminary" in the last paragraph of section
      11.1 feels wrong; I would reword this to 'precomposition with a
      renaming'.

* [X] Some of the capitalization in the references is off, e.g. Miniagda,
      Poplmark, coq.

fixed those three.

# Review 3 "detailed comments"

* [X] p.1: There should be an indication that the paper uses color on the
           first page, so that readers make sure to use an appropriate printer.

put a footnote in the abstract.

* [X] p.1: "Capture avoiding substitution" should be "capture-avoiding
      substitution" (also search the rest of the file)

done. Only instance I believe.

* [X] p.1: "well-scopedness" is missing the hyphen. This is an issue
      throughout the article - please do a search.

Adverbs modify adjectives perfectly well without assistance from a hyphen.

* [X] p.2: "ill-scoped" and "ill-typed" are missing their hyphens

see above.

* [X] p.2: "Related Work" should not be capitalized, as it's not used as a
       proper noun here

* [X] p.2: The paragraph beginning with "Breaking the task down" refers to
  an implementor, also referred to with the pronoun "they". The
  paragraph right after the numbered list, that begins with "Even
  after", uses the pronoun "you" to refer to the
  implementor. Consistency is necessary, and "they" seems better here.

* [X] p.2: The citation of Benton et al is in parentheses, but it's used as
      an ordinary noun phrase and thus should not be parenthesized.

* [X] p.2, last line: "Fusable" should probably be "fusible"

* [ ] p.3: This page states that the techniques are language-independent,
      requiring only inductive families, but it seems to me that the use of
      sized types is a key part of making the fixed point construction go
      through. Is that not the case?

Cf. clarification in letter.md. Do we want to include this discussion
somewhere in the paper? Certainly not on page 3!

* [X] p.4: The line "We use Agda's" seems to be a part of the paragraph
      prior to the example of _-Scoped, so it should not be indented.

* [ ] p.4: Here's a chance to explain the naming conventions. The _-Scoped
      family is named with a leading hyphen, and used in postfix position,
      as if it were ML, but many other types are used in prefix. How were
      the operators to use in postfix selected? Does the hyphen just
      indicate that it's postfix, or does it mean something else? It would
      be useful to explain these kinds of naming conventions, to help
      readers understand the code by understanding the conventions used.

* [X] p.4: The citation of "Martin-Löf (1982)" has far too many parentheses
      around it. In this case, it's a noun phrase - use \citet or the
      equivalent.

* [X] p.5: The turnstile notation (\_⊢\_) seems a bit obscure. Please consider
      adding an explanation of why it was chosen to help readers remember
      its meaning later on.

* [X] p.5: The claim that these notations are more readable is not
      immediately clear from this page, but it does seem to be the case
      later on, with the exception of the somewhat confusing turnstile
      notation.

* [ ] p.5: In the definition of Var, small sigma occurs free. This is
      usually not allowed in Agda. In the online code, this is done with a
      "variable" declaration - please consider putting this declaration in
      the article as well, or at least having a table with the corresponding
      declarations (esp. because e.g. sigma is used as a locally bound
      variable, while alpha is used as a datatype constructor, and only the
      color distinguishes these cases in the typesetting)

* [X] p.5: It would be nice if the \_$\_ notation were explained, or if
      ordinary parentheses were used. Not everyone who works with dependent
      types is a major Haskell user.

* [ ] p6: The notation (Γ -Env) Var Δ was a source of confusion,
      initially. It seems to mix postfix and ordinary notation. Why can't
      Env just come first?

DISCUSS: have we at any point argued about what the most lucid
notation for all these concepts might be? Informally, we use \subseteq
for Thinnings, and in my cover versions with Craig of original ACMM, I
used \Vdash (variants of?) for substitutions. Regarding the infix
nature of the definition, I would happily write

 \Gamma \Vdash[ V ] \Delta for (\Gamma -Env) V \Delta

and specialise, where needed, eg V = Var.

Any takers?

* [X] p6: Missing comma after "Thinnables" on the last line

* [ ] p7: Fig. 2 is in a float, which means that the figure is
      left-justified. This looks very different from the Thinning definition
      earlier on the page, which is centered. There's a repeated issue in
      the article where there seems to be no pattern governing which code
      ends up in a figure and which ends up in a centered display box, and
      where the captions on figures have inconsistent font coloration and
      capitalization with respect to the main text.

SOLUTION: use the new agdasnippet environment for non-figure code blocks.
Need an additional reading of the **whole** paper to detect all occurences
of similar problems.

* [ ] p7: Fig 2 uses copatterns. These are introduced and cited much later
      in the article, but they're used here. Please move their introduction
      to the first place they're used. Copatterns are also used in both
      prefix notation and with the dotted projection notation - picking one
      and explaining it clearly would increase the accessibility of the
      paper to non-Agda-experts.

* [X] p8: The uses of script V and script C at the top of the page should be
      after their introductions halfway down the page.

They already are.

* [X] p8, code: the code on page 8 seems to be mostly part of the record
      Semantics, but this took some reverse engineering. Can the fields be
      indented, as they would be in Agda? And are definitions like extend
      (e.g. manifest fields) allowed as part of a record? If so, say so, and
      make it clear which code is in the record body.

* [X] p8: When talking about the Kripke function space in NbE, please cite
      it so interested readers can follow up.

* [X] p8, last sentence: This sentence has a very complicated
      structure. What about a rewrite like "Agda allows us to package a
      generic traversal function "semantics" together with the fields of the
      record "Semantics", which causes it to be brought into scope for any
      instance of "Semantics".". And how is this different from having a
      field with a function type?

* [X] p8: This page has the first name that contains a caret (^). Please
      explain this naming convention - how should the caret be understood
      and pronounced? Is it intended to imply a superscript?

* [X] p9: At the beginning of 3.3, it would be nice to remind readers that,
      in the arguments to Semantics, the first argument is what gets
      substituted, and the second is the syntax being operated over. These
      sorts of little high-level descriptions would make the paper much less
      laborious to read.

* [X] p9: The sentence starting with "To print a variable" should be there
      to match the rest of the syntax, but it's not.

* [X] p9: "so it is automatically a Thinnable functor" - is this reflected
      in any code? Is this standing for an implementation of th^V?

* [X] p.10: The code in Fig 6 uses do-notation, but the code in Fig. 7 does
      not. The do-notation seems much easier to read. Can it be used in
      Fig. 7?

* [X] p.10: "Inductive-Recursive" should be lowercase

* [X] p.11: A high-level description of the roles played by I and J in Desc
      would be useful. Why are there two parameters?

* [X] p.11: "Indexes" should probably read "indices", esp. in an article
      using UK English

* [X] p.12: Later, on p. 15, the paper says that Agda uses pattern synonyms
      to resugar output. This discussion should perhaps occur here, at the
      first use of pattern synonyms.

* [X] p.16: "records explicitly the change" -> "explicitly records the change"

* [X] p.16: Here's another name with a ^ in it, still unexplained

* [ ] p. 17: When something is called a lemma, it should have an English
      statement in addition to the encoding in Agda. This would make it much
      easier to figure out.

* [X] p. 18: There is a sentence "We immediately introduce a corollary ...",
      but it's not clear where that happens. This corollary should be in the
      text, rather than in a float on the next page, and it should also have
      an English statement that readers can compare to the Agda.

* [ ] p. 19: Earlier uses of copatterns did them as prefix projections,
      Fig. 30 uses postfix.

* [X] p. 19: The sentence starting with "Hence, we can then implement..."
      trails off at a colon without ever being finished.

* [X] p. 20: The name M referred to here is defined on page 6. It would be
      best to give it a more memorable name, but failing that, it would be
      good to have an explicit page reference for its binding site so
      readers can go remind themselves of what it means.

Renamed to Fresh (+ added back link)

* [X] p. 20: Couldn't parse the sentence "Wrapper it is Thinnable, and fresh
      (defined in Fig. 6) is the proof that we can generate placeholder
      values thanks to the name supply."

* [ ] p.21: A sentence each describing mapA and sequenceA would be useful here.

* [X] p.22: "consist in type checking" -> "consists of type checking"

* [X] p. 23: The sentence "Terms in the raw syntax ..." was a bit hard to
      follow. Consider more commas, or breaking it in two.

broken up into three.

* [X] p.23: I-dec could use a description/definition in the text

* [X] p.24: "bi-directional" shouldn't be hyphenated

      also "bi-sorted" -> "bisorted"

* [X] p.25: The constructor name alpha didn't get mentioned before this
      page. Consider including a definition of Type somewhere.

* [X] p.25: "check the input type is" -> "check that the input type is"

* [X] p.25: The use of the term "cut" for the annotated embedding of
      checkable into inferrable terms is not widespread - consider
      explaining it here.

* [X] p.25: The alphas toward the bottom of the page should be in
      constructor font (green)

* [X] p.26: "During typechecking we generate at the same time an
      expression's type ..." -> "During typechecking we simultaneously
      generate an expression's type ..."

* [X] p.26: Couldn't parse "We can then explain what it means for
      elaboration to target T a (Type -Scoped) at a type sigma:". It looks
      like the variable T has type (Type -Scoped) in the code, but the rest
      confused me.

* [X] p.27: "do-notation" should be singular, not plural (do a search of the
      article)

* [X] p.27: The overloading in the definition of isArrow is confusing. Could
      one arrow be made different, perhaps the one in the view?

No. But added an explanation.

* [ ] p. 28: What is bind again? The code b (bind Infer) (epsilon dot var_0)
      (sigma :: Gamma) tau was pretty opaque.

* [X] p. 28: Consider the phrasing "Luckily, Agda's dependent do-notation
      makes our job easy once again:".

* [X] p.29: The patterns `IN and `IN' were difficult to distinguish at first

* [X] p.30: In figure 51, what is "pack"?

* [X] p.30: Hyphenate "size-preserving" and "size-respecting"

no

* [X] p.31: Redex is short for "reducible expression" - it's not a Latin
      word, so it should be pluralized "redexes".

* [X] p.32: "and computations are the pairing" --> "and whose computations
      are the pairing"

* [X] p.35: "much of the standard traversals" -> "many of the standard
      traversals" (because "traversal" is grammatically countable)

* [ ] p.36: Copattern matching is introduced here, after it's been used
      numerous times already. Also, more extraneous parentheses in the
      citations.

* [X] p.37: "premisse" -> "premise"



* [X] p.38:  "generic" is repeated in the last line of the page.

done (also spotted by reviewer 1).

* [X] p.39: "and decision procedure can be defined" -> "and decision
      procedures can be defined"

* [X] p.39: The code in figure 72 is the first time the articule used lambda
      as an argument without either using $ or parentheses. When that's
      paired up with the where syntax, consider some extraneous parentheses.

done

* [X] p.40: What does it mean to have a module definition inside a record?
      Please explain this.

fixed by splitting up the definition of Simulation.

* [X] p.40: Break the sentence at "; which we have experience" and write "We
      experience this first hand when tackling..." as a new sentence.



* [X] p.41: "Results which" -> "Results that" (because it's a restrictive
      use)

fixed

* [X] p.42: "prevents to try to prove for instance that" occurs in a very
      long, run-on sentence. Consider reformulating the sentence to
      something like "Nothing prevents proofs, such as the idempotence of
      NbE, which use a bona fide reification function that extracts terms
      from model values"

 much better indeed!

* [X] p.43: The parenthesis opened after "on that term is related via" and
      before Kripke is never closed.



* [X] p.43: "This set of constraint" -> "This set of constraints"

fixed.

* [X] p.43: The font in Fusion changes after the s, and it doesn't seem to
      be a reference to an identifier Fus in this article.

 Also multiple instances of Sim.

* [X] p.45: "the appropriate notion of Semantics" seems to have "Semantics"
      in the wrong font.

rendered as inline code.

* [X] p. 46: "of each combinators" -> "of each combinator"

* [X] p. 46: The article should discuss how related work is related, not
      just list the fact that it is related. But the discussion of Back
      Poulsen et al doesn't discuss that relationship.

Fair enough. Also added a discussion of Cheney.

* [X] p.47: The vertical gap above 10.5 is very large.

* [X] p.47: Why are Pickering et al cited for Agda's pattern synonyms?
      Haskell's are much younger, and what's described in the cited paper.

Asked Adam at last SPLS, it is true that Agda's came first.

* [X] p.47: "but also sum" -> "but also sums"

* [X] p.49: Under "closure under products" and "unrestricted variables", the
      word "kind" is used the way that "sort" was used in most of the
      article

* [X] p.50: "well-behaved" needs a hyphen

see above.
