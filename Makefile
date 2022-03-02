AGDA ?= agda
.PHONY: listings clean

default: everything

everything:
	$(AGDA) -i. -isrc Everything.agda

listings:
	$(AGDA) -i. -isrc --html README.agda -v0

clean:
	find . -type f -name '*.agdai' -delete
