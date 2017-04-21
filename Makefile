SRCS=$(wildcard *.v)
OBJS=$(SRCS:.v=.vo)

all: $(OBJS)

Translation.vo : Translation.v ImpS.vo ImpE.vo

IdTrans.vo : IdTrans.v ImpS.vo ImpE.vo
	coqc $<

ImpS.vo: ImpS.v Common.vo
	coqc $<

ImpE.vo: ImpE.v Common.vo
	coqc $<

Common.vo: Common.v
	coqc $<

clean:
	rm -f *.vo *.glob .*.vo.aux

.PHONY: all clean
