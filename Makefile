ImpE.vo : ImpE.v Common.vo
	coqc $<

Common.vo : Common.v
	coqc $<

clean:
	rm -f *.vo *.glob .*.vo.aux

.PHONY: clean
