#!/bin/sh
./CC tests/$1 && spim -file "tests/$1.asm"
#java -jar Mars.jar tests/$1.asm
