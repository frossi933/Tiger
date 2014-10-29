#!/bin/bash
# testTiger carpetaTiger carpetaTests

CASOS=`ls $2`
for i in $CASOS; do
	echo "···prueba···"
	echo $i
	$1/tiger $2/$i
	echo "next:"
	read s;
done
	
