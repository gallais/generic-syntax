1\begin{code}
module Generic where

-- Module re-exporting pretty much everything that can be useful

-- Notations, auxiliary notions
import indexed
open module idx = indexed public
import var as V
open module var = V public hiding (_<$>_)
open import pred as P
open module pred = P public hiding (∀[_])
open import rel as R
open module rel = R public hiding (∀[_])
import varlike
open module vlk = varlike public
import environment
open module env = environment public hiding (traverse)

-- The generic library itself
import Generic.Syntax
open module syn = Generic.Syntax public
import Generic.Semantics
open module sem = Generic.Semantics public
import Generic.Zip
open module zip = Generic.Zip public
import Generic.Simulation
open module sim = Generic.Simulation public hiding (RenSub ; rensub)
import Generic.Fusion
import Generic.Fundamental
open module fdm = Generic.Fundamental public
open module fus = Generic.Fusion public
import Generic.Identity
open module idt = Generic.Identity public

-- Instances
import Generic.Semantics.Unit
open module uni = Generic.Semantics.Unit public
import Generic.Examples.NbyE
open module nbe = Generic.Examples.NbyE public
import Generic.Examples.Printing
open module prt = Generic.Examples.Printing public
\end{code}
