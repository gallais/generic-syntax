--------------------------------------------------------------------------------
-- This module precisely maps sections in the paper to Agda modules
--------------------------------------------------------------------------------

module TableOfContent where

--------------------------------------------------------------------------------
-- 1. Introduction
--------------------------------------------------------------------------------

-- The motivating problem for the paper is solved twice:
-- * Once by writing a lot of boilerplate
-- * Once by using the library, thus skipping directly to the interesting parts

import Motivation.Problem.Naive
import Motivation.Problem.WithLibrary

--------------------------------------------------------------------------------
-- 2. A Primer on Scope and Sort Safe Terms
--------------------------------------------------------------------------------

-- The combinators to build indexed types are introduced in
import Stdlib

-- The generic notion of well scoped-and-sorted variable is defined in
import Data.Var

-- The well scoped-and-typed STLC is defined in
import StateOfTheArt.ACMM

--------------------------------------------------------------------------------
-- 3. A Primer on Type and Scope Safe Programs
--------------------------------------------------------------------------------

-- The similar-looking type-and-scope safe traversals (renaming, substitution,
-- but also normalization by evaluation) are also defined in
import StateOfTheArt.ACMM

-- Environments and Thinnings are available in
import Data.Environment

-- The generic notion of Semantics and its fundamental lemma as well as the
-- various instances (renaming, substitution, printing) are in
import StateOfTheArt.ACMM

--------------------------------------------------------------------------------
-- 4. A Primer on the Universe of Data Types
--------------------------------------------------------------------------------

-- The whole section refers to content in
import StateOfTheArt.CDMM

--------------------------------------------------------------------------------
-- 5. A Universe of Scope Safe and Well Sorted Syntaxes
--------------------------------------------------------------------------------

-- The Universe, the meaning of its codes as relative functors and terms of a
-- syntax with binding as free relative-monads over that functor are all in
import Generic.Syntax

-- The examples of (Untyped/Simply-Typed) Lambda Calculus are in
import Generic.Syntax.UTLC
import Generic.Syntax.STLC

-- The common combinators (and their properties) are all in
import Generic.Syntax

--------------------------------------------------------------------------------
-- 6. Generic Scope Safe Well Sorted Programs for Syntaxes
--------------------------------------------------------------------------------

-- The generic notion of a Semantics together with its fundamental lemma are in
import Generic.Semantics

-- The Kripke function space is defined in
import Data.Environment using (Kripke)

-- The generic definition of Renaming and Substitution as instances of Sem can
-- be found in
import Generic.Semantics.Syntactic

-- For the reification of the Kripke Spaces back to Scopes they rely on
import Data.Var.Varlike

--------------------------------------------------------------------------------
-- 7. A Catalogue of Generic Programs for Syntax with Binding
--------------------------------------------------------------------------------

-- 7.1 Sugar and Desugaring as a Semantics

-- Single let binders are defined as a description in
import Generic.Syntax.LetBinder

-- The elaboration semantics inlining let binders is in
import Generic.Semantics.Elaboration.LetBinder

-- 7.2 (Unsafe) Normalization by Evaluation

-- The non-strictly positive domain, reification and normalization functions are
-- all in:
import Generic.Semantics.NbyE

-- The application to normalizing the Untyped Lambda Calculus is in
import Generic.Examples.NbyE

-- 7.3 An Algebraic Approach to Typechecking

-- The specific bidirectional language at hand is defined in
import Generic.Syntax.Bidirectional

-- The Typechecker itself is in
import Generic.Semantics.TypeChecking

-- 7.4 Binding as Self-Reference: Reprensenting Cyclic Structures

-- The example of potentially cyclic lists is in
import Generic.Examples.Colist

-- The generic notion of a potentially infinite tree and the unrolling function are
-- defined in
import Generic.Cofinite

--------------------------------------------------------------------------------
-- 8. Building Generic Proofs about Generic Programs
--------------------------------------------------------------------------------

-- The relation transformer is in:
import Generic.Relator

-- 8.1 Simulation Lemma

-- The relational version of the Kripke function space is in
import Data.Var.Varlike using (Kripkeᴿ)

-- The simulation framework and its fundamental lemma are in
import Generic.Simulation

-- The proof that renaming and substitution are extensional, and that renaming
-- is a form of substitution are in
import Generic.Simulation.Syntactic

-- 8.2 Fusion Lemma

-- The fusion constraints and the fundamental lemma of fusions are in
import Generic.Fusion

-- The instances proving that substitution and renaming can be fused every which way
-- are all in
import Generic.Fusion.Syntactic

-- The compatibility of Renaming, Substitution, and Let-inlining is demonstrated in
import Generic.Fusion.Elaboration.LetBinder

-- The replicated result of Kaiser, Schäfer, and Stark relying on the axiom
-- of functional extensionality is in
import Generic.Fusion.Specialised.Replication

-- 8.3 Definition of Bisimilarity for co-finite objects

-- The notion and its properties are established in
import Generic.Bisimilar

-- The examples are in
import Generic.Examples.Colist
