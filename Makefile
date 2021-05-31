EXTRA_DIR:=extra
COQDOCFLAGS:= \
  --external 'http://ssr2.msr-inria.inria.fr/doc/ssreflect-1.5/' Ssreflect \
  --external 'http://ssr2.msr-inria.inria.fr/doc/mathcomp-1.5/' MathComp \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS

.PHONY: all coq clean html
all: coq

fundamental: Makefile.coq
	$(MAKE) -f Makefile.coq pretty-timed only TGTS="theories/fundamental.vo"

fundamental-binary: Makefile.coq
	$(MAKE) -f Makefile.coq pretty-timed only TGTS="theories/binary_model/fundamental_binary.vo"

coq: Makefile.coq
	$(MAKE) -f Makefile.coq pretty-timed

html: Makefile.coq
	rm -rf html
	$(MAKE) -f Makefile.coq html
	cp $(EXTRA_DIR)/resources/* html

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -rf html
