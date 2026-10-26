COQBIN ?=
COQC ?= $(COQBIN)coqc
COQMAKEFILE := $(COQBIN)coq_makefile
COQPROJECT := _CoqProject
COQMF := Makefile.coq
JOBS ?= 2

.PHONY: all build clean audit test check-coq check-build check-models check-c check-c-evidence fetch-source source-audit config-audit source-inventory source-inventory-check status

all: build

$(COQMF): $(COQPROJECT)
	$(COQMAKEFILE) -f $(COQPROJECT) -o $(COQMF)

check-coq:
	@$(COQBIN)coqc --version | head -n 1 | grep -Eq 'version 8\.18\.0( |$$)' || \
	  { echo 'This project requires Coq 8.18.0.' >&2; exit 1; }

build: check-coq $(COQMF)
	$(MAKE) -f $(COQMF) -j$(JOBS) COQC="$(COQC)"

clean:
	@if [ -f $(COQMF) ]; then $(MAKE) -f $(COQMF) clean; fi
	rm -f $(COQMF) Makefile.coq.conf

fetch-source:
	./scripts/fetch-v293-source.sh

source-audit:
	python3 scripts/audit-v293-upstream.py

config-audit:
	python3 scripts/build-v293-config.py \
	  csrc/upstream/v2.93.01/checkout/Cfg/Template/os_cfg.h \
	  csrc/upstream/v2.93.01/checkout/os_cfg.h

source-inventory: source-audit
	python3 scripts/inventory-v293-source.py

source-inventory-check: source-audit
	python3 scripts/inventory-v293-source.py --check

audit:
	python3 scripts/project-audit.py
	python3 scripts/coverage-audit.py

test: source-audit
	python3 -m unittest discover -s tests -v

check-models:
	COQBIN="$(COQBIN)" bash scripts/check-v293-models.sh

check-c: source-audit
	python3 scripts/check-v293-c-regressions.py

check-c-evidence: source-audit
	python3 scripts/check-v293-c-regressions.py --check-report audit/c-regressions.json

check-build:
	COQBIN="$(COQBIN)" JOBS="$(JOBS)" bash scripts/check-clean-build.sh

status:
	@echo 'Coq sources:' $$(find framework tactics certiucos/v293 -name '*.v' | wc -l)
	@echo 'V293 sources:' $$(find certiucos/v293 -name '*.v' | wc -l)
	@git status --short --branch
