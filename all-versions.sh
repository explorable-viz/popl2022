#!/bin/bash
set -e

# make sure script runs in directory that contains it
HERE="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
cd $HERE

./build.sh anonymised
./build.sh anonymised-full
./build.sh final-full
