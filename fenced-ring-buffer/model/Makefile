SOURCES=$(wildcard *.tla)
PLANTUML_SOURCES=$(wildcard *.plantuml)

WORKERS := 4

TLA := java -XX:+UseParallelGC -cp tla2tools.jar
TLC := ${TLA} tlc2.TLC
PLUSCAL := ${TLA} pcal.trans
TLATEX := ${TLA} tla2tex.TLA

PLANTUML := java -jar plantuml.jar

.PHONY: all check pdfs

all: check pdfs

tla2tools.jar:
	wget -nc "https://github.com/tlaplus/tlaplus/releases/download/v1.6.0/tla2tools.jar"

%.check: %.tla %.cfg tla2tools.jar
	[ -d metadir/check/$* ] || mkdir -p metadir/check/$*

	@echo "\n\n--------- MAYBE PLUSCAL --------------"
	(grep -q "\-\-algorithm" $*.tla && ${PLUSCAL} $*.tla) || true

	@ echo "\n\n-------------- TLC ------------------"
	${TLC} -workers ${WORKERS} -metadir metadir/check/$* $*.tla 2>&1 | tee $@.tmp
	@ echo "-------------------------------------\n\n"
	@! grep "Error:" $@.tmp
	mv $@.tmp $@

%.pdf: %.tla tla2tools.jar
	[ -d metadir/pdf/$* ] || mkdir -p metadir/pdf/$*
	@ echo "\n\n------------ TLATEX ----------------"
	${TLATEX} -shade -latexCommand pdflatex -latexOutputExt pdf -metadir metadir/pdf/$* $*.tla
	@ echo "-------------------------------------\n\n"

plantuml.jar:
	wget -nc "https://astuteinternet.dl.sourceforge.net/project/plantuml/plantuml.jar"

%.svg: %.plantuml plantuml.jar
	@ echo "\n\n------------ PLANTUML ----------------"
	${PLANTUML} -tsvg -pipe < $*.plantuml > $*.svg
	@ echo "-------------------------------------\n\n"

check: $(SOURCES:.tla=.check)
pdfs: $(SOURCES:.tla=.pdf)
diagrams: $(PLANTUML_SOURCES:.plantuml=.svg)

clean:
	rm -rf metadir states
	rm -f *.check *.pdf