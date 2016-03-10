SRCFILES := $(shell find src/ -name '*.java')
CLASSFILES := $(patsubst src/%.java,bin/%.class,$(SRCFILES))

all: $(CLASSFILES)
	@echo -n "" 

bin/%.class: src/%.java 
	@echo -n $< " "

