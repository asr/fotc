AGDA = agda -v 0
RSYNC = rsync --archive --progress --rsh='ssh -p 2024'

# Host directory used by publish
# Tunneling connection
root_host_dir = asicard@localhost:tmp

clean :
	-find -name '*.agdai' | xargs rm -f
	-rm -f /tmp/*.tptp
