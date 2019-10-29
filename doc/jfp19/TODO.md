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

* [ ] p.4: The line "We use Agda's" seems to be a part of the paragraph
      prior to the example of _-Scoped, so it should not be indented.

* [ ] p.4: Here's a chance to explain the naming conventions. The _-Scoped
      family is named with a leading hyphen, and used in postfix position,
      as if it were ML, but many other types are used in prefix. How were
      the operators to use in postfix selected? Does the hyphen just
      indicate that it's postfix, or does it mean something else? It would
      be useful to explain these kinds of naming conventions, to help
      readers understand the code by understanding the conventions used.

* [ ] p.4: The citation of "Martin-Löf (1982)" has far too many parentheses
      around it. In this case, it's a noun phrase - use \citet or the
      equivalent.

* [ ] p.5: The turnstile notation (_⊢_) seems a bit obscure. Please consider
      adding an explanation of why it was chosen to help readers remember
      its meaning later on.

* [ ] p.5: The claim that these notations are more readable is not
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

* [ ] p.5: It would be nice if the _$_ notation were explained, or if
      ordinary parentheses were used. Not everyone who works with dependent
      types is a major Haskell user.

* [ ] p6: The notation (Γ -Env) Var Δ was a source of confusion,
      initially. It seems to mix postfix and ordinary notation. Why can't
      Env just come first?

* [ ] p6: Missing comma after "Thinnables" on the last line

* [ ] p7: Fig. 2 is in a float, which means that the figure is
      left-justified. This looks very different from the Thinning definition
      earlier on the page, which is centered. There's a repeated issue in
      the article where there seems to be no pattern governing which code
      ends up in a figure and which ends up in a centered display box, and
      where the captions on figures have inconsistent font coloration and
      capitalization with respect to the main text.

* [ ] p7: Fig 2 uses copatterns. These are introduced and cited much later
      in the article, but they're used here. Please move their introduction
      to the first place they're used. Copatterns are also used in both
      prefix notation and with the dotted projection notation - picking one
      and explaining it clearly would increase the accessibility of the
      paper to non-Agda-experts.

* [ ] p8: The uses of script V and script C at the top of the page should be
      after their introductions halfway down the page.

* [ ] p8, code: the code on page 8 seems to be mostly part of the record
      Semantics, but this took some reverse engineering. Can the fields be
      indented, as they would be in Agda? And are definitions like extend
      (e.g. manifest fields) allowed as part of a record? If so, say so, and
      make it clear which code is in the record body.

* [ ] p8: When talking about the Kripke function space in NbE, please cite
      it so interested readers can follow up.

* [ ] p8, last sentence: This sentence has a very complicated
      structure. What about a rewrite like "Agda allows us to package a
      generic traversal function "semantics" together with the fields of the
      record "Semantics", which causes it to be brought into scope for any
      instance of "Semantics".". And how is this different from having a
      field with a function type?

* [ ] p8: This page has the first name that contains a caret (^). Please
      explain this naming convention - how should the caret be understood
      and pronounced? Is it intended to imply a superscript?

* [ ] p9: At the beginning of 3.3, it would be nice to remind readers that,
      in the arguments to Semantics, the first argument is what gets
      substituted, and the second is the syntax being operated over. These
      sorts of little high-level descriptions would make the paper much less
      laborious to read.

* [ ] p9: The sentence starting with "To print a variable" should be there
      to match the rest of the syntax, but it's not.

* [ ] p9: "so it is automatically a Thinnable functor" - is this reflected
      in any code? Is this standing for an implementation of th^V?

* [ ] p.10: The code in Fig 6 uses do-notation, but the code in Fig. 7 does
      not. The do-notation seems much easier to read. Can it be used in
      Fig. 7?

* [ ] p.10: "Inductive-Recursive" should be lowercase

* [ ] p.11: A high-level description of the roles played by I and J in Desc
      would be useful. Why are there two parameters?

* [ ] p.11: "Indexes" should probably read "indices", esp. in an article
      using UK English

* [ ] p.12: Later, on p. 15, the paper says that Agda uses pattern synonyms
      to resugar output. This discussion should perhaps occur here, at the
      first use of pattern synonyms.

* [ ] p.16: "records explicitly the change" -> "explicitly records the change"

* [ ] p.16: Here's another name with a ^ in it, still unexplained

* [ ] p. 17: When something is called a lemma, it should have an English
      statement in addition to the encoding in Agda. This would make it much
      easier to figure out.

* [ ] p. 18: There is a sentence "We immediately introduce a corollary ...",
      but it's not clear where that happens. This corollary should be in the
      text, rather than in a float on the next page, and it should also have
      an English statement that readers can compare to the Agda.

* [ ] p. 19: Earlier uses of copatterns did them as prefix projections,
      Fig. 30 uses postfix.

* [ ] p. 19: The sentence starting with "Hence, we can then implement..."
      trails off at a colon without ever being finished.

* [ ] p. 20: The name M referred to here is defined on page 6. It would be
      best to give it a more memorable name, but failing that, it would be
      good to have an explicit page reference for its binding site so
      readers can go remind themselves of what it means.

* [ ] p. 20: Couldn't parse the sentence "Wrapper it is Thinnable, and fresh
      (defined in Fig. 6) is the proof that we can generate placeholder
      values thanks to the name supply."

* [ ] p.21: A sentence each describing mapA and sequenceA would be useful here.

* [ ] p.22: "consist in type checking" -> "consists of type checking"

* [ ] p. 23: The sentence "Terms in the raw syntax ..." was a bit hard to
      follow. Consider more commas, or breaking it in two.

* [ ] p.23: I-dec could use a description/definition in the text

* [ ] p.24: "bi-directional" shouldn't be hyphenated

* [ ] p.25: The constructor name alpha didn't get mentioned before this
      page. Consider including a definition of Type somewhere.

* [ ] p.25: "check the input type is" -> "check that the input type is"

* [ ] p.25: The use of the term "cut" for the annotated embedding of
      checkable into inferrable terms is not widespread - consider
      explaining it here.

* [ ] p.25: The alphas toward the bottom of the page should be in
      constructor font (green)

* [ ] p.26: "During typechecking we generate at the same time an
      expression's type ..." -> "During typechecking we simultaneously
      generate an expression's type ..."

* [ ] p.26: Couldn't parse "We can then explain what it means for
      elaboration to target T a (Type -Scoped) at a type sigma:". It looks
      like the variable T has type (Type -Scoped) in the code, but the rest
      confused me.

* [ ] p.27: "do-notation" should be singular, not plural (do a search of thea
      article)

* [ ] p.27: The overloading in the definition of isArrow is confusing. Could
      one arrow be made different, perhaps the one in the view?

* [ ] p. 28: What is bind again? The code b (bind Infer) (epsilon dot var_0)
      (sigma :: Gamma) tau was pretty opaque.

* [ ] p. 28: Consider the phrasing "Luckily, Agda's dependent do-notation
      makes our job easy once again:".

* [ ] p.29: The patterns `IN and `IN' were difficult to distinguish at first

* [ ] p.30: In figure 51, what is "pack"?

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

* [ ] p.40: What does it mean to have a module definition inside a record?
      Please explain this.

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

* [ ] p.47: The vertical gap above 10.5 is very large.

* [ ] p.47: Why are Pickering et al cited for Agda's pattern synonyms?
      Haskell's are much younger, and what's described in the cited paper.

* [X] p.47: "but also sum" -> "but also sums"

* [X] p.49: Under "closure under products" and "unrestricted variables", the
      word "kind" is used the way that "sort" was used in most of the
      article

* [X] p.50: "well-behaved" needs a hyphen

see above.
