.PHONY: build-log manage-features try-compile

build-log:
	python3 scripts/build-log.py

manage-features:
	python3 scripts/manage-features.py

try-compile:
	python3 scripts/try-compile.py
