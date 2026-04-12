#!/bin/sh

mkdir -p 'doc/assets'

rm -rf 'doc/trees/autogen'
mkdir -p 'doc/trees/autogen'

rm -rf 'output/html'
mkdir -p 'output/html'

cp -f 'theme/Agda.css' 'output/html/'
