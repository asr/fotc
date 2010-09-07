# Includes
TOP = ..
include $(TOP)/mk/config.mk

# Tunneling connection
host_dir = asicard@localhost:tmp/LTC/

local_path = LTC

conjectures :
	cd .. && ./test-conjectures.bash LTC

type_checking :
	cd .. && $(AGDA) $(local_path)/Everything.agda

type_checking_ER :
	cd .. && $(AGDA) $(local_path)/EverythingER.agda

type_checking_all : type_checking_ER type_checking

test : type_checking_all conjectures

publish :
	rm -r -f html/

	cd .. && \
	$(AGDA) --html --html-dir=$(local_path)/html \
		$(local_path)/Everything.agda

	$(RSYNC) html/ $(host_dir)

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
