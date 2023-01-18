SUBMIT := src/
ZIPNAME := hw_submission.zip

all:
	dune build

.PHONY: test
test:
	dune runtest

zip: clean $(SUBMIT)
	zip '$(ZIPNAME)' -r $(SUBMIT)

.PHONY: clean
clean:
	dune clean

.PHONY: utop
utop:
	dune utop
