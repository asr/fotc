# Tunneling connection
host_dir = asicard@localhost:./tmp/Logic/
port = 2024

AGDA = agda -v 0
local_path = Examples/Logic

conjectures :
	cd ../.. && ./test-conjectures.bash Logic

type_checking :
	cd ../.. && $(AGDA) $(local_path)/Logic.agda

type_checking_all : type_checking

test : type_checking_all conjectures

publish :
	rm -r -f html/
	cd ../.. && \
	$(AGDA) --html --html-dir=$(local_path)/html \
		$(local_path)/Logic.agda

	scp -P $(port) -r html/ $(host_dir)

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
