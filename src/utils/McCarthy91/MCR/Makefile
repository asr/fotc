FLAGS = -Wall -Werror

source = MCR

build : $(source).hs
	stack ghc -- $(FLAGS) --make $< -o /tmp/mcr
clean :
	rm -f $(source).hi $(source).o
