AGDA = agda -v 0 --ignore-interfaces

std_lib_path = ~/agda-upstream/std-lib/src

tests :
	$(AGDA) -itest test/NoImports.agda
	cd test && dump-agdai NoImports.agda

	$(AGDA) -itest -i $(std_lib_path) test/Imports.agda
	cd test && dump-agdai Imports.agda

	$(AGDA) -itest test/SortedOutput.agda
	cd test && dump-agdai SortedOutput.agda
