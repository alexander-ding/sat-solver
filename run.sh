#!/bin/bash

E_BADARGS=65
if [ $# -ne 1 ]
then
	echo "Usage: `basename $0` <input>"
	exit $E_BADARGS
fi
	
input=$1

julia --project=@. --optimize=3 --inline=yes --math-mode=fast src/Main.jl $input
