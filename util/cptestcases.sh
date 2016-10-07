#!/bin/bash
# Copy all the testcases from GLH
# Original files from GLH:
# ===================================
# SRS_L2C_SYN_001/
# --ast_output.txt
# --config.txt
# --Expected
# --readme.txt
# --SRS_L2C_SYN_001.lustre
# ====================================
# SRS-SEM-NUM.format:	naming rules
# sem-xxx.ast		ast file
# ====================================
# SRS_L2C_SYN_001/ast_output.txt --> OspreyTest/SingleSource/syn_001.ast




CASES=`find ./test -name "*.ast" | sort`


for j in $CASES; do
	dstj=`echo $j | sed -e 's/\.\/test\///' `
	dstj=`echo $dstj | sed -e 's/\.\/test\/SCADE_ERROR/scade_error/' `
	dstj=`echo $dstj | sed -e 's/\/SRS_L2C.*/\.ast/' | sed -e 's/\//\_/' `
	dstj=`echo $dstj | sed -e 's/\_scade_error.*/\.ast/' | sed -e 's/\//\_/' `
	echo "copy $j to ./OspreyTest/SingleSource/$dstj"
	cp -rf $j ./OspreyTest/SingleSource/$dstj
	#dos2unix ./OspreyTest/SingleSource/$dstj
	#for some linux distribution use tofrodos tools
	fromdos ./OspreyTest/SingleSource/$dstj
done

CASES1=`find ./test -name "*.lustre"`


for i in $CASES1; do
	dsti=`echo $i | sed -e 's/\.\/test\///' `
	dsti=`echo $dsti | sed -e 's/\.\/test\/SCADE_ERROR/scade_error/' `
	dsti=`echo $dsti | sed -e 's/\/SRS_L2C.*/\.lustre/' | sed -e 's/\//\_/' `
	dsti=`echo $dsti | sed -e 's/\_scade_error.*/\.lustre/' | sed -e 's/\//\_/' `
	#echo "copy $i to ./OspreyTest/SingleSource/$dsti"
	cp -rf $i ./OspreyTest/SingleSource/$dsti
	#dos2unix ./OspreyTest/SingleSource/$dstj
	#for some linux distribution use tofrodos tools
	fromdos ./OspreyTest/SingleSource/$dsti
done

