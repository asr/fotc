FLAGS = -Wall -Werror

source = ManyAxioms

$(source).agda : $(source).hs
	ghc $(FLAGS) $< -o /tmp/many-axioms
	/tmp/many-axioms > /tmp/$(source).agda

clean :
	rm -f $(source)
	rm -f $(source).hi
	rm -f $(source).o
