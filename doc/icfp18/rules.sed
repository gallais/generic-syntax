# Super- and subscripts.
## fix to make it work with Agda 2.4.2.4
s/\\textasciicircum\([^{]\)/\\textasciicircum\{\}\1/g
## Usual rules
s/‿\([^\}]*\)\\textasciicircum{}\([^\}]*\)/\^\{\\AgdaFontStyle\{\\scriptscriptstyle \2\}\}\_\{\\AgdaFontStyle\{\\scriptscriptstyle \1\}\}/g
s/\\textasciicircum{}\([^.\}]*\)‿\([^\}]*\)/\^\{\\AgdaFontStyle\{\\scriptscriptstyle \1\}\}\_\{\\AgdaFontStyle\{\\scriptscriptstyle \2\}\}/g
s/\\textasciicircum{}\([^.\}]*\)/\{\\textsuperscript\{\\AgdaFontStyle\{\\scriptsize \1\}\}\}/g
s/{\([^{.]*\)\({\^\\AgdaFontStyle{\\scriptscriptstyle{}[^\]*}\)/\{\{\1\}\2/g
s/‿\([^\}]*\)/\\textsubscript\{\\AgdaFontStyle\{\\scriptsize \1\}\}/g

# Set levels
s/\\AgdaSymbol{(}[^:]*\\AgdaSymbol{:} \\AgdaPostulate{Level}\\AgdaSymbol{)} \\AgdaSymbol{→} //g
s/[ ]*\\AgdaBound{ℓ}//g
s/[ ]*\\AgdaBound{ℓ′}//g
s/[ ]*\\AgdaBound{ℓ′′}//g
s/\\AgdaPrimitive{L.suc}//g
s/[ ]*\\AgdaPrimitive{⊔}[ ]*//g
s/ \?\\AgdaBound{{ℓ}{[^{]*{[^{]*{}[^}]*}}}//g
s/\\AgdaSymbol{(}\\AgdaSymbol{)}//g
s/ \\AgdaSymbol{(}\\AgdaSymbol{))}/\\AgdaSymbol\{)\}/g

# Operators
s/>>=/\$\\mathbin\{>\\!\\!>\\mkern-6.7mu=\}\$/g
s/>>/\$\\mathbin\{>\\!\\!>}\$/g
s/++/\$+\\!+\$/g
s/==/\$=\\!=\$/g

# Pointwise things
s/⟶/\$\\,\\dot\{\\to\}\\,\$/g
s/∙⊎/\$\\dot\{\\uplus\}\$/g
s/∙×/\$\\dot\{\\times\}\$/g
s/κ/\$\\kappa\$/g

# Latex
#s/^\\begin{code}/\\begin\{code\}\\defaultcolumn{l}\n\\\\/g
#s/^\\end{code}/\\\\\\end\{code\}\n/g
s/^\\begin{code}/\\begin\{code\}\\defaultcolumn{l}/g

# Implicit arguments
s/\\AgdaSymbol{λ} \\AgdaSymbol{\\{}\\AgdaBound{σ}\\AgdaSymbol{\\}} \\AgdaSymbol{\\{}\\AgdaBound{τ}\\AgdaSymbol{\\}} \\AgdaSymbol{→} //g
#s/\\AgdaSymbol{\\{}\\AgdaBound{σ}\\AgdaSymbol{\\}} \\AgdaSymbol{\\{}\\AgdaBound{τ}\\AgdaSymbol{\\};}/\\AgdaSymbol{;}/g
s/\\AgdaSymbol{λ} \\AgdaSymbol{\\{}\\AgdaBound{σ}\\AgdaSymbol{\\}} \\AgdaSymbol{→} //g
s/\\AgdaSymbol{\\{}\\AgdaBound{p}\\AgdaSymbol{\\}} //g
s/^\([^∀]*\)\\AgdaSymbol{\\{}[^<∀𝓡]*\\AgdaSymbol{\\}}\([^<∀=]*\)\\AgdaSymbol{=}/\1\2\\AgdaSymbol{=}/g
s/^\([^∀]*\)\\AgdaSymbol{\\{}[^<𝓡∀]*\\AgdaSymbol{\\}}[^<()→𝓡∀;]*\\AgdaSymbol{→} /\1/g
s/^\([^∀]*\)\\AgdaSymbol{\\{}[^<()𝓡∀;]*\\AgdaSymbol{\\}}/\1/g
s/^\([^∀]*\)\\AgdaSymbol{\\{}[^<;𝓡∀]*\\AgdaSymbol{\\}}/\1/g

# Hacks
s/`→/`\\!\\!→/g
s/`1/`\\!1/g
s/`2/`\\!2/g
#s/𝓡/\\mathcal{R}/g
s/𝓔/\\mathcal\{E\}/g
s/𝓜/\\mathcal\{M\}/g
s/𝓢/$\\mathcal\{S\}$/g
s/𝓒\(_.\)/\$\\mathcal\{C\1\}\$/g
s/𝓒/\$\\mathcal\{C\}\$/g
s/𝓥\(_.\)/\$\\mathcal\{V\1\}\$/g
s/𝓥/\$\\mathcal\{V\}\$/g
s/ε/\$\\varepsilon\{\}\$/g
s/\\AgdaField{rel}//g
# Sorry
s/\\AgdaSymbol{\\{}\\AgdaArgument{s} \\AgdaSymbol{=} \\AgdaBound{s}\\AgdaSymbol{\\}}//g

# Anti-unicode
s/─/--/g
s/∷/::/g
s/σ/\$\\sigma\$/g
s/τ/\$\\tau\$/g
s/Γ/\$\\Gamma\$/g
s/Δ/\$\\Delta\$/g
s/ρ/\$\\rho\$/g
s/⟦/\$\\llbracket\$/g
s/⟧/\$\\rrbracket\$/g
s/→/\$\\to\$/g
s/∎/\$\\blacksquare\$/g
s/Σ/\$\\Sigma\$/g
s/Θ/\$\\Theta\$/g
s/Ξ/\$\\Xi\$/g
s/ˡ/\\textsuperscript\{l\}/g
s/ʳ/\\textsuperscript\{r\}/g
s/↺/\$\\circlearrowleft\{\}\$/g
s/↶/\$\\curvearrowleft\{\}\$/g
s/δ/\$\\delta\$/g
s/𝓡/$\\mathcal{R}$/g