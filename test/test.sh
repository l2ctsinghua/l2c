#! /bin/bash

cd test

if [ ! -d "result" ]
then
    mkdir result;
fi

files=`find ./cases/ -name "*.ast"`
for f in $files
do
    if [[ $f =~ ^\./cases/([^\.]+)\.ast$ ]]
    then
	echo $f;
	mkdir result/${BASH_REMATCH[1]};
	../l2c -target_dir result/${BASH_REMATCH[1]} $f;
    else
	echo "Not propper format";
    fi
done

cd ..
