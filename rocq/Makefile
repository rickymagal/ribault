COQMAKEFILE := $(shell command -v rocq >/dev/null 2>&1 && echo "rocq makefile" || echo coq_makefile)

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject Syntax.v Interp.v Typing.v Safety.v Dfg.v Trans.v TransFacts.v TransAgree.v TransSafety.v
	$(COQMAKEFILE) -f _CoqProject -o Makefile.coq

clean:
	-$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

.PHONY: all clean
