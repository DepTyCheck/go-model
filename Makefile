.PHONY: build-log manage-features try-compile

build-log:
	sh scripts/build-log.sh

manage-features:
	python3 scripts/manage-features.py

try-compile:
	python3 scripts/try-compile.py
