#!/bin/bash
set -e

./build.sh anonymised
./build.sh anonymised-full
./build.sh final-full
