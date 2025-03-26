.PHONY: build-log

build-log:
	stdbuf -oL pack build | tee "logs/log_$$(date +"%m-%d_%H-%M").txt"
