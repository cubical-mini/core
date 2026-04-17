#!/bin/sh

PR=${PR:-$PWD}

forester build "$PR/forest.toml"
