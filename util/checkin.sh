#!/bin/bash
# find the check in times
echo " "
echo "Checkin Times Statistic till `date +%Y%m%d`"
echo " Times  Member:"
svn log -q | grep 201 | tr '\011' ' ' | tr -s " "| cut -d' ' -f3 | sort |uniq -c |sort -nbr | tee _tmp_checkin_log.txt
echo -n " Totally `svn info | grep Revision |  cut -d' ' -f2` checkins"
echo " by `wc _tmp_checkin_log.txt |  cut -d' ' -f2` developers"
rm -rf _tmp_checkin_log.txt
