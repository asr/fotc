# Tunneling connection
host_dir = asicard@localhost:./tmp/LTC/
port = 2024

agda-path = /home/asr/code/phd/LTC/LTC-ATP/

conjectures :
	./test-conjectures.bash

conjecturesPCF :
	./test-conjecturesPCF.bash

only-type-checking :
	agda -i $(agda-path) EverythingER.agda
	agda -i $(agda-path) Everything.agda

test : only-type-checking conjectures conjecturesPCF

publish :
	rm -r -f html/
	agda --html -i $(agda-path) Everything.agda
	scp -P $(port) -r html/ $(host_dir)

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
