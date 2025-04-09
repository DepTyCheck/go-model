.PHONY: build-log manage-features try-compile

build-log:
	python scripts/build-log.py

manage-features:
	python scripts/manage-features.py

try-compile:
	python scripts/try-compile.py
