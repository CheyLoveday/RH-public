MANUSCRIPT := papers/type-i-torsion/manuscript
SOURCE_DATE_EPOCH := 1795564800
export SOURCE_DATE_EPOCH

.PHONY: all reading pdf check-reading

all: reading pdf

reading:
	python3 scripts/github_reading.py

pdf:
	pandoc --from=markdown --pdf-engine=tectonic $(MANUSCRIPT)/paper.md -o $(MANUSCRIPT)/paper.pdf

check-reading:
	python3 scripts/github_reading.py --check
