module Generic where

--------------------------------------------------------------------------------
-- MOTIVATION
--------------------------------------------------------------------------------

-- Expository problem described in the paper: two languages (S with lets, T without),
-- an elaboration from S to T, two operational semantics and a desired proof:
-- a simulation lemma between a term s in S and its elaboration in T.

import Motivation.Problem.Naïve
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
import indexed

-- SYNTAX
--------------------------------------------------------------------------------

-- Variables as well scoped-and-sorted de Bruijn indices
import var as V
import varlike

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


-- SEMANTICS
--------------------------------------------------------------------------------

-- Environments as Well Scoped-and-Sorted Functions from Variables to Values
import environment

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
import Generic.Semantics.Elaboration.LetBinders

-- Specific Semantics relating various examples of Syntaxes
import Generic.Semantics.TypeChecking
import Generic.Semantics.Elaboration.State


-- PROPERTIES
--------------------------------------------------------------------------------

-- Zip: Head Constructors with Related Subterms
import Generic.Zip

-- Fundamental Lemma of Logical Predicates
import pred as P
import Generic.Fundamental

-- Generic Notion of Simulation Between Two Semantics
import rel as R
import Generic.Simulation
import Generic.Simulation.Syntactic

-- Applying the Identity Substitution is the Identity
import Generic.Identity

-- Generic Notion of Fusible Semantics
import Generic.Fusion
import Generic.Fusion.Syntactic
import Generic.Fusion.Elaboration.LetBinder



-- SYNTAX AS A FINITE REPRESENTATION OF CYCLIC STRUCTURES
--------------------------------------------------------------------------------

import Generic.Cofinite
import Generic.Examples.Colist
import Generic.Bisimilar




-- Offering users convenient short names
open module idx = indexed public
open module var = V public hiding (_<$>_)
open module pred = P public hiding (∀[_])
open module rel = R public hiding (∀[_])
open module vlk = varlike public
open module env = environment public hiding (traverse)
open module syn = Generic.Syntax public
open module sem = Generic.Semantics public
open module zip = Generic.Zip public
open module sim = Generic.Simulation public
open module fdm = Generic.Fundamental public
open module fus = Generic.Fusion public
open module idt = Generic.Identity public

open module uni = Generic.Semantics.Unit public
open module nbe = Generic.Semantics.NbyE public
open module prt = Generic.Semantics.Printing public
