stanovsky :
	cd ~/code/phd/FOT && \
	agda -i. -isrc Draft/DistributiveLaws/TaskB-ATP.agda && \
	agda2atp -i. -isrc --only-files \
	         Draft/DistributiveLaws/TaskB-ATP.agda

	mv /tmp/Draft.DistributiveLaws.TaskB-ATP.prop2_12.tptp ./stanovsky.tptp
	~/src/TPTP/TPTP-v5.1.0/TPTP2X/tptp2X -fwaldmeister -d. stanovsky.tptp

clean :
	rm -f *.agdai *.pr *.tptp


