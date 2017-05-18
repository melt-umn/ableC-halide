# Top-level directory containing ableC repository and extensions folder
EXT_HOME=../../..

# The jar file to built
ABLEC_JAR=ableC.jar
# The artifact specification grammar to compile
ARTIFACT=artifact
# All directories containing grammars that may be included
GRAMMAR_DIRS=$(wildcard $(EXT_HOME)/extensions/*/grammars) $(EXT_HOME)/ableC
# All silver files in included grammars, to be included as dependancies
GRAMMAR_SOURCES=$(shell find $(GRAMMAR_DIRS) -name *.sv -print0 | xargs -0)
# Flags passed to silver including the appropriate directories
SVFLAGS=$(addprefix -I , $(GRAMMAR_DIRS))

# All extended C files to compile
XC_FILES=$(wildcard *.xc)
# All C files that should be generated
C_FILES=$(XC_FILES:.xc=.c)
# All object files that should be generated
OBJECTS=$(XC_FILES:.xc=.o)
# All executables that should be generated
EXECUTABLES=$(XC_FILES:.xc=.out)
# All evaluation marker files that should be generated
TESTS=$(XC_FILES:.xc=.test)

XC_INCLUDE_DIRS=$(wildcard $(EXT_HOME)/extensions/*/include)
XCFLAGS=$(addprefix -I, $(XC_INCLUDE_PATH))

LIB_DIRS=$(wildcard $(EXT_HOME)/extensions/*/lib)
LDLIBS=$(addprefix -L, $(LIB_DIRS))

all: $(ABLEC_JAR) $(C_FILES) $(OBJECTS) $(EXECUTABLES) $(TESTS)

$(ABLEC_JAR): $(GRAMMAR_SOURCES)
	touch $(wildcard $(ARTIFACT)/*.sv)
	silver -o $@ $(SVFLAGS) $(ARTIFACT)

%.c: %.xc $(ABLEC_JAR)
	java -jar $(ABLEC_JAR) $< $(XCFLAGS)

%.out: %.o
	$(CC) $(LDFLAGS) $< $(LOADLIBES) $(LDLIBS) -o $@

%.test: %.out
	@echo "Running $<..."
	@./$< || echo "(exit $$?)"
	touch $@

clean:
	rm -f *~ *.i *.c *.o *.out *.test *.jar *.copperdump.html build.xml

.PHONY: all clean
