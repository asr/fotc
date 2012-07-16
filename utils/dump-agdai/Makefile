AGDA = agda -v 0 --ignore-interfaces

# TODO: 13 July 2012. Why ~/... doesn't work?
std_lib_path = /home/asr/src/agdas/agda-upstream/std-lib/src

tests :
#       A file without imports.
	$(AGDA) -itest test/NoImports.agda
	cd test && dump-agdai NoImports.agda

#       A file with an import from the standard library.
	$(AGDA) -itest -i$(std_lib_path) test/Imports.agda
	cd test && dump-agdai Imports.agda
