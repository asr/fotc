# Includes
TOP = ../..
include $(TOP)/mk/config.mk

# Tunneling connection
host_dir = asicard@localhost:tmp/GCD/

local_path = Examples/GCD

conjectures :
	cd ../.. && ./test-conjectures.bash GCD

type_checking :
	cd ../.. && $(AGDA) $(local_path)/ProofSpecification.agda

type_checking_ER :
	cd ../.. && $(AGDA) $(local_path)/ProofSpecificationER.agda

type_checking_all : type_checking_ER type_checking

test : type_checking_all conjectures

publish :
	rm -r -f html/

	cd ../.. && \
	$(AGDA) --html --html-dir=$(local_path)/html \
		$(local_path)/ProofSpecification.agda

	$(RSYNC) html/ $(host_dir)

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
