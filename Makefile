SRCS=$(wildcard *.v)
OBJS=$(SRCS:.v=.vo)

all: $(OBJS)

#ImpE2.vo: ImpE2.v ImpE.vo Common.vo
#	coqc $<

ImpS.vo: ImpS.v Common.vo
	coqc $<

ImpE.vo: ImpE.v Common.vo
	coqc $<

Common.vo: Common.v
	coqc $<

clean:
	rm -f *.vo *.glob .*.vo.aux

.PHONY: all clean
