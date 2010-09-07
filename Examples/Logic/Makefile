# Includes
TOP = ../..
include $(TOP)/mk/config.mk

# Tunneling connection
host_dir = asicard@localhost:tmp/Logic/

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

	$(RSYNC) html/ $(host_dir)

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
