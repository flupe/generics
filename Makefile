AGDA ?= agda
.PHONY: listings clean

default: listings

listings:
	$(AGDA) -i. -isrc --html README.agda -v0

clean:
	find . -type f -name '*.agdai' -delete
