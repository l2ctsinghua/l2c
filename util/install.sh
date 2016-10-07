#!/bin/bash

TOOLROOT=~/bin
export PATH=$TOOLROOT:$PATH

MKDIR="/bin/mkdir -p"
$MKDIR ${TOOLROOT}

INSTALL="/usr/bin/install"
$INSTALL ./l2c ${TOOLROOT}/l2c

echo "l2c INSTALL to $TOOLROOT"
echo "PATH is: `echo $PATH`"
l2c -version
