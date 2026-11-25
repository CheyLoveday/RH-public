MANUSCRIPT := papers/type-i-torsion/manuscript
SOURCE_DATE_EPOCH := 1795564800
export SOURCE_DATE_EPOCH

.PHONY: all reading pdf guide check-reading check-guide

all: reading pdf guide

reading:
	python3 scripts/github_reading.py

pdf:
	pandoc --from=markdown --pdf-engine=tectonic $(MANUSCRIPT)/paper.md -o $(MANUSCRIPT)/paper.pdf

guide:
	python3 scripts/illustrated_guide.py

check-reading:
	python3 scripts/github_reading.py --check

check-guide:
	python3 scripts/illustrated_guide.py --check
