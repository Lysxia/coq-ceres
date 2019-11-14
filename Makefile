.PHONY: coq test build install clean html cleanall

MF_COQ := Makefile.coq

build: $(MF_COQ)
	$(MAKE) -f $(MF_COQ)

install: build
	$(MAKE) -f $(MF_COQ) install

test: build
	coqc -Q theories/ Ceres test/Test.v

_CoqProject:
	ln -s _CoqProject.classic _CoqProject

$(MF_COQ): _CoqProject
	coq_makefile -f _CoqProject -o $(MF_COQ)

clean:
	if [ -e $(MF_COQ) ] ; then make -f $(MF_COQ) cleanall ; fi
	$(RM) */*.{vo,glob} */.*.aux $(MF_COQ){,.conf}

cleanall: clean
	$(RM) _CoqProject

COQDOCJS_DIR := coqdocjs

COQDOCFLAGS = \
  -t "Ceres" \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(COQDOCJS_DIR)/extra/header.html --with-footer $(COQDOCJS_DIR)/extra/footer.html

export COQDOCFLAGS

html: Makefile.coq coq
	rm -rf html
	$(MAKE) -f Makefile.coq html
	cp $(COQDOCJS_DIR)/extra/resources/* html
