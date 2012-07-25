source = ManyAxioms

$(source).agda : $(source).hs
	ghc --make $< -o /tmp/many-axioms
	/tmp/many-axioms > /tmp/$(source).agda
