#!/bin/sh

set -eu

pack update-db
pack switch latest
pack install-deps
pack build
