SRCS=$(wildcard *.v)
OBJS=$(SRCS:.v=.vo)

all: $(OBJS)

SImpESecurity.vo: SImpESecurity.v SImpE2TypeSystem.vo SImpE2Adequacy.vo SImpE2Helpers.vo SImpE2.vo SImpE.vo SImpECommon.vo
	coqc $<

SImpE2TypeSystem.vo: SImpE2TypeSystem.v SImpE2Adequacy.vo SImpE2SecurityHelpers.vo SImpE2Helpers.vo SImpE2.vo SImpE.vo SImpECommon.vo
	coqc $<

SImpE2SecurityHelpers.vo : SImpE2SecurityHelpers.v SImpE2Adequacy.vo SImpE2Helpers.vo SImpE2.vo SImpE.vo SImpECommon.vo
	coqc $<

SImpE2Adequacy.vo: SImpE2Adequacy.v SImpE2Helpers.vo SImpE2.vo SImpE.vo SImpECommon.vo
	coqc $<

SImpE2Helpers.vo : SImpE2Helpers.v SImpE2.vo SImpE.vo SImpECommon.vo
	coqc $<

SImpE2.vo: SImpE2.v SImpE.vo SImpECommon.vo
	coqc $<

SImpE.vo: SImpE.v SImpECommon.vo
	coqc $<

SImpECommon.vo: SImpECommon.v
	coqc $<

clean:
	rm -f *.vo *.glob .*.vo.aux

.PHONY: all clean
