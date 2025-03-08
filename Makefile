build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
