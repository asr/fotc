# Tunneling connection
host_dir = asicard@localhost:./tmp/Logic/
port = 2024

AGDA = agda -v 0
local-path = Examples/Logic

conjectures :
	cd ../.. && ./test-conjectures.bash Logic

type-checking :
	cd ../.. && $(AGDA) $(local-path)/Logic.agda

type-checking-all : type-checking

test : type-checking-all conjectures

publish :
	rm -r -f html/
	cd ../.. && \
	$(AGDA) --html --html-dir=$(local-path)/html \
		$(local-path)/Logic.agda

	scp -P $(port) -r html/ $(host_dir)

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
