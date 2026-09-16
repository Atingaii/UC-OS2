COQBIN ?=
COQMAKEFILE := $(COQBIN)coq_makefile
COQPROJECT := _CoqProject
COQMF := Makefile.coq
JOBS ?= 2

.PHONY: all build clean audit fetch-source source-audit config-audit status

all: build

$(COQMF): $(COQPROJECT)
	$(COQMAKEFILE) -f $(COQPROJECT) -o $(COQMF)

build: $(COQMF)
	$(MAKE) -f $(COQMF) -j$(JOBS)

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

audit:
	python3 scripts/project-audit.py
	python3 scripts/coverage-audit.py

status:
	@echo 'Coq sources:' $$(find framework tactics certiucos/v293 -name '*.v' | wc -l)
	@echo 'V293 sources:' $$(find certiucos/v293 -name '*.v' | wc -l)
	@git status --short --branch
