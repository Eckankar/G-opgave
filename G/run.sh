#!/bin/sh
./CC tests/$1 #&& spim -file "tests/$1.asm"
if [ -e "tests/$1.in" ]; then
    java -jar Mars.jar tests/$1.asm < tests/$1.in
else
    java -jar Mars.jar tests/$1.asm
fi

