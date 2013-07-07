MODULES := Equiv Order Complex ComplexTheorems AbelianGroup AbelianGroupTheorems Field Scalar Vector State InnerProd
VS      := $(MODULES:%=Lib/%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R Lib Lib $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
