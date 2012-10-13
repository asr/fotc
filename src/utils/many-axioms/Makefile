FLAGS = -Wall -Werror

source = ManyAxioms

$(source).agda : $(source).hs
	ghc $(FLAGS) --make $< -o /tmp/many-axioms
	/tmp/many-axioms > /tmp/$(source).agda

clean :
	rm -f $(source).hi $(source).o
