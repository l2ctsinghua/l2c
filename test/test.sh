#! /bin/bash

cd test

if [ ! -d "result" ]
then
    mkdir result;
fi

files=`find ./cases/ -name "*.ast"`
for f in $files
do
    name=`echo $f | cut -d'/' -f 3 | cut -d'.' -f 1`;
    echo $f;
    rm -rf result/$name;
    mkdir result/$name;
    ../l2c -target_dir result/$name $f;
done

cd ..
