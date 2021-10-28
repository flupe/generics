AGDA ?= agda
.PHONY: listings clean

listings:
	$(AGDA) -i. -isrc --html README.agda -v0

clean:
	find . -type f -name '*.agdai' -delete
