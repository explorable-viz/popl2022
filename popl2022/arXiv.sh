#!/bin/bash
set -e

NAME=arXiv.zip
zip -r $NAME .
zip -d $NAME *.pdf
zip -d $NAME fig/.DS_Store
zip -d $NAME .DS_Store

unzip -l $NAME
