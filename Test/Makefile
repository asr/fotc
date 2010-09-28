TOP = ..
include $(TOP)/mk/config.mk

local_path = Test

conjectures :
	cd $(TOP) && ./Test/conjectures.bash Test

type_checking :
	cd $(TOP) && $(AGDA) $(local_path)/LambdaLifting.agda

type_checking_all : type_checking

all : type_checking_all conjectures
