#!/bin/bash

set -e

rm -rf cm* CM* lib* Testing* tests* include tests compile_commands.json Makefile KCBox
cmake -DENABLE_PYTHON_INTERFACE=ON -DENABLE_TESTING=ON -DCMAKE_EXPORT_COMPILE_COMMANDS=ON ..
make -j4
rm -rf cm* CM* lib* Testing* tests* include tests compile_commands.json Makefile
