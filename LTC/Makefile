# Tunneling connection
host_dir = asicard@localhost:./tmp/LTC/
port = 2024

AGDA = agda -v 0
agda-path = /home/asr/code/phd/LTC/LTC-ATP/

conjectures :
	./test-conjectures.bash

conjecturesPCF :
	./test-conjecturesPCF.bash

only-type-checking :
	$(AGDA) -i $(agda-path) EverythingER.agda
	$(AGDA) -i $(agda-path) Everything.agda

test : only-type-checking conjectures conjecturesPCF

publish :
	rm -r -f html/
	$(AGDA) --html -i $(agda-path) Everything.agda
	scp -P $(port) -r html/ $(host_dir)

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
