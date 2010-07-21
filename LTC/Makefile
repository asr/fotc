# Tunneling connection
host_dir = asicard@localhost:./tmp/LTC/
port = 2024

AGDA = agda -v 0
local-path = LTC

conjectures :
	cd .. && ./test-conjectures.bash LTC

conjecturesPCF :
	cd .. && ./test-conjectures.bash LTC-PCF

type-checking :
	cd .. && $(AGDA) $(local-path)/Everything.agda

type-checking-ER :
	cd .. && $(AGDA) $(local-path)/EverythingER.agda

type-checking-all : type-checking-ER type-checking

test : type-checking-all conjectures conjecturesPCF

publish :
	rm -r -f html/

	cd .. && \
	$(AGDA) --html --html-dir=$(local-path)/html \
		$(local-path)/Everything.agda

	scp -P $(port) -r html/ $(host_dir)

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
