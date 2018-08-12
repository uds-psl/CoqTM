all: Makefile.coq
	+make -f Makefile.coq all

html: Makefile.coq
	mkdir -p website/resources
	cp -rf external/coqdocjs/extra/resources/* external/coqdocjs/extra/*.html website/
	+make -f Makefile.coq html
	mv html/*html website
	rm -rf html

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f website/*html

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject > Makefile.coq
	echo ".PHONY: html" >> Makefile.coq

.PHONY: all html clean


#Costum alterations:

%.vo: Makefile.coq
	+make -f Makefile.coq $@
