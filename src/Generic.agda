module Generic where

-- Notations for indexed types
import indexed


-- SYNTAX
--------------------------------------------------------------------------------

-- Variables as well scoped-and-sorted de Bruijn indices
import var as V
import varlike

-- Universe of Well Scoped-and-Sorted Syntaxes with Binding
import Generic.Syntax


-- SEMANTICS
--------------------------------------------------------------------------------

-- Environments as Well Scoped-and-Sorted Functions from Variables to Values
import environment

-- Semantics as Well Scoped-and-Sorted Algebras on Syntaxes with Binding
import Generic.Semantics

-- Examples
import Generic.Semantics.Unit
import Generic.Examples.NbyE
import Generic.Examples.Printing

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

-- Applying the Identity Substitution is the Identity
import Generic.Identity

-- Generic Notion of Fusible Semantics
import Generic.Fusion




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
open module sim = Generic.Simulation public hiding (RenSub ; rensub)
open module fdm = Generic.Fundamental public
open module fus = Generic.Fusion public
open module idt = Generic.Identity public

open module uni = Generic.Semantics.Unit public
open module nbe = Generic.Examples.NbyE public
open module prt = Generic.Examples.Printing public
