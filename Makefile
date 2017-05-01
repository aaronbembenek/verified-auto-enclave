SRCS=$(wildcard *.v)
OBJS=$(SRCS:.v=.vo)

all: $(OBJS)

ImpE2Security.vo: ImpE2Security.v ImpE2TypeSystem.vo ImpE2Adequacy.vo ImpE2Helpers.vo ImpE2.vo ImpE.vo Common.vo
	coqc $<

ImpE2TypeSystem.vo: ImpE2TypeSystem.v ImpE2Adequacy.vo ImpE2SecurityHelpers.vo ImpE2Helpers.vo ImpE2.vo ImpE.vo Common.vo
	coqc $<

ImpE2SecurityHelpers.vo : ImpE2SecurityHelpers.v ImpE2Adequacy.vo ImpE2Helpers.vo ImpE2.vo ImpE.vo Common.vo
	coqc $<

ImpE2Adequacy.vo: ImpE2Adequacy.v ImpE2Helpers.vo ImpE2.vo ImpE.vo Common.vo
	coqc $<

ImpE2Helpers.vo : ImpE2Helpers.v ImpE2.vo ImpE.vo Common.vo
	coqc $<

ImpE2.vo: ImpE2.v ImpE.vo Common.vo
	coqc $<

ImpE.vo: ImpE.v Common.vo
	coqc $<

Common.vo: Common.v
	coqc $<

clean:
	rm -f *.vo *.glob .*.vo.aux

.PHONY: all clean
