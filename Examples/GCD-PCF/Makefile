# Tunneling connection
host_dir = asicard@localhost:./tmp/GCD-PCF/
port = 2024

AGDA = agda -v 0
agda-path = /home/asr/code/phd/LTC/LTC-ATP/

conjecturesPCF :
	./test-conjecturesPCF.bash

only-type-checking :
	$(AGDA) -i $(agda-path) ProofSpecificationPCF-ER.agda
	$(AGDA) -i $(agda-path) ProofSpecificationPCF.agda

test : only-type-checking conjecturesPCF

publish :
	rm -r -f html/
	$(AGDA) --html -i $(agda-path) ProofSpecificationPCF.agda
	scp -P $(port) -r html/ $(host_dir)

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
