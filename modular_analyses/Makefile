# Top-level directory containing ableC repository and extensions folder
EXT_HOME=../../..
# All directories containing grammars that may be included
GRAMMAR_DIRS=$(wildcard $(EXT_HOME)/extensions/*/grammars) $(EXT_HOME)/ableC
# Flags passed to silver including the appropriate directories
SVFLAGS=$(addprefix -I , $(GRAMMAR_DIRS))

all: mda mwda

mda:
	touch $(wildcard determinism/*.sv)
	silver -o MDA.jar $(SVFLAGS) --clean determinism

mwda:
	touch $(wildcard well_definedness/*.sv)
	silver -o MWDA.jar $(SVFLAGS) --clean --warn-all --warn-error well_definedness

clean:
	rm -f *~ *.jar *.copperdump.html build.xml

.PHONY: all mda mwda clean
