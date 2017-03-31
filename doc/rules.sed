# Operators
s/>>=/\\mathbin\{>\\!\\!>\\mkern-6.7mu=\}/g
s/>>/\\mathbin\{>\\!\\!>}/g
s/++/+\\!+/g

# Pointwise things
s/⟶/\\,\\dot\{→\}\\,/g
s/∙⊎/\\dot\{⊎\}/g
s/∙×/\\dot\{×\}/g

# Latex
#s/^\\begin{code}/\\begin\{code\}\n\\\\/g
#s/^\\end{code}/\\\\\\end\{code\}\n/g

# Implicit arguments
s/\\AgdaSymbol{λ} \\AgdaSymbol{\\{}\\AgdaBound{σ}\\AgdaSymbol{\\}} \\AgdaSymbol{\\{}\\AgdaBound{τ}\\AgdaSymbol{\\}} \\AgdaSymbol{→} //g
s/\\AgdaSymbol{\\{}\\AgdaBound{σ}\\AgdaSymbol{\\}} \\AgdaSymbol{\\{}\\AgdaBound{τ}\\AgdaSymbol{\\};}/\\AgdaSymbol{;}/g
s/\\AgdaSymbol{λ} \\AgdaSymbol{\\{}\\AgdaBound{σ}\\AgdaSymbol{\\}} \\AgdaSymbol{→} //g
s/\\AgdaSymbol{\\{}\\AgdaBound{σ}\\AgdaSymbol{\\}} //g
s/\\AgdaSymbol{\\{}[^<]*\\AgdaSymbol{\\}}\([^<=]*\)\\AgdaSymbol{=}/\1\\AgdaSymbol{=}/g
s/\\AgdaSymbol{\\{}[^<]*\\AgdaSymbol{\\}}[^<()→;]*\\AgdaSymbol{→} //g
s/\\AgdaSymbol{\\{}[^<();]*\\AgdaSymbol{\\}}//g
s/\\AgdaSymbol{\\{}[^<;]*\\AgdaSymbol{\\}}//g

# Hacks
s/`→/`\\!\\!→/g
s/`1/`\\!1/g
s/`2/`\\!2/g
s/𝓡/\\mathcal{R}/g
s/𝓔/\\mathcal\{E\}/g
s/𝓜/\\mathcal\{M\}/g
s/𝓢/\\mathcal\{S\}/g
s/𝓒/\\mathcal\{C\}/g
s/𝓥/\\mathcal\{V\}/g
s/ε/\\varepsilon\{\}/g
