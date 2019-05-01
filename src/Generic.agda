module Generic where

--------------------------------------------------------------------------------
-- STATE OF THE ART
--------------------------------------------------------------------------------

-- This work relies on previous efforts in dependently-typed programming:
-- CDMM defines a generic universe of datatypes
import StateOfTheArt.CDMM
-- ACMM defines a generic notion of semantics for a well scoped-and-typed language
import StateOfTheArt.ACMM

--------------------------------------------------------------------------------
-- MOTIVATION
--------------------------------------------------------------------------------

-- Expository problem described in the paper: two languages (S with lets, T without),
-- an elaboration from S to T, two operational semantics and a desired proof:
-- a simulation lemma between a term s in S and its elaboration in T.

import Motivation.Problem.Naive
import Motivation.Problem.WithLibrary

-- Solutions to the POPLMark Reloaded challenge: proving using a logical relation
-- argument the strong normalization of the Simply Typed Lambda Calculus, its
-- extensions with Sums, and finally Gödel T.

import Motivation.POPLMark2.STLC
import Motivation.POPLMark2.Sums
import Motivation.POPLMark2.GodelT


--------------------------------------------------------------------------------
-- THE LIBRARY
--------------------------------------------------------------------------------

-- Notations for indexed types
import Stdlib

-- SYNTAX
--------------------------------------------------------------------------------

-- Variables as well scoped-and-sorted de Bruijn indices
import Data.Var as V
import Data.Var.Varlike

-- Universe of Well Scoped-and-Sorted Syntaxes with Binding
import Generic.Syntax

-- Examples of Syntaxes
-- * Well-scoped UnTyped Lambda-Calculus
import Generic.Syntax.UTLC
-- * Well-scopde-and-phased Bidirectional UnTyped Lambda-Calculus
import Generic.Syntax.Bidirectional
-- * Well-scoped-and-typed variants of the Simply-Typed Lambda-Calculus
import Generic.Syntax.STLC
import Generic.Syntax.STLC+State
import Generic.Syntax.STLC+Product
-- * System F as a two-phase syntax
import Generic.Examples.SystemF

-- Syntax extensions (single / counted / parallel) let-binders
import Generic.Syntax.LetBinder
import Generic.Syntax.LetCounter
import Generic.Syntax.LetBinders


-- Alternative interpretation of descriptions empower us to write:

-- A converter to PHOAS syntax
open import Generic.Syntax.PHOAS

-- A generic scope checker converting raw terms to well scoped terms
open import Generic.Scopecheck

-- SEMANTICS
--------------------------------------------------------------------------------

-- Environments as Well Scoped-and-Sorted Functions from Variables to Values
import Data.Environment

-- Semantics as Well Scoped-and-Sorted Algebras on Syntaxes with Binding
import Generic.Semantics

-- Trivial instance of a Semantics
import Generic.Semantics.Unit

-- Renaming and Substitution as Semantics
import Generic.Semantics.Syntactic

-- Generic Unsafe Normalization by Evaluation and Printing as Semantics
import Generic.Semantics.NbyE
import Generic.Semantics.Printing
-- use cases:
import Generic.Examples.NbyE
import Generic.Examples.Printing

-- Generic Elaboration of Let-binders (single & parallel ones)
import Generic.Semantics.Elaboration.LetBinder
import Generic.Semantics.Elaboration.LetCounter
import Generic.Semantics.Elaboration.LetBinders

-- Specific Semantics relating various examples of Syntaxes
import Generic.Semantics.TypeChecking
import Generic.Semantics.Elaboration.State
import Generic.Semantics.Elaboration.Typed

-- PROPERTIES
--------------------------------------------------------------------------------

-- Relator: Head Constructors with Related Subterms
import Generic.Relator

-- Fundamental Lemma of Logical Predicates
import Data.Pred as P
import Generic.Fundamental

-- Generic Notion of Simulation Between Two Semantics
import Data.Relation as R
import Generic.Simulation
import Generic.Simulation.Syntactic

-- Applying the Identity Substitution is the Identity
import Generic.Identity

-- FUSION

-- Generic Notion of Fusible Semantics
import Generic.Fusion

-- Renaming and Substitution interact well with each other and let-elaboration
import Generic.Fusion.Syntactic
import Generic.Fusion.Elaboration.LetBinder

-- Based on Kaiser, Schäfer, and Stark's remark, we can concoct an axiom-free
-- specialised version of fusion for renaming-semantics interactions (it makes
-- some of the previous proofs shorter).
-- We can also use it to replicate their result assuming functional extensionality
import Generic.Fusion.Specialised.Propositional
import Generic.Fusion.Specialised.Replication



-- SYNTAX AS A FINITE REPRESENTATION OF CYCLIC STRUCTURES
--------------------------------------------------------------------------------

import Generic.Cofinite
import Generic.Examples.Colist
import Generic.Bisimilar

