# Tunneling connection
host_dir = asicard@localhost:./tmp/SortList/
port = 2024

# Agda path
agda-path = /home/asr/code/phd/LTC/LTC-ATP/

conjectures :
	./test-conjectures.bash

only-type-checking :
	agda -i $(agda-path) Closures/ListER.agda
	agda -i $(agda-path) PropertiesER.agda
	agda -i $(agda-path) ProofSpecificationER.agda
	agda -i $(agda-path) ProofSpecification.agda

test : only-type-checking conjectures

publish :
	rm -r -f html/
	agda --html -i /home/asr/code/phd/LTC/LTC-ATP/ ProofSpecification.agda
	scp -P $(port) -r html/ $(host_dir)
