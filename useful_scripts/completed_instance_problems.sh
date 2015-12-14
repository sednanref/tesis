#!/bin/bash

conf=$1;
file=SUMMARY.${conf}.cplex.cost;

echo "" > ${conf}_problems.csv

cat  $file | cut -d"/" -f1 | awk '!x[$0]++' > temp.txt;

for line in  `cat temp.txt`; do 
    echo -n ${line}, >> ${conf}_problems.csv;
    #echo $line >>${conf}_problems.csv;
    grep "^${line}" ${file} | wc -l 1>> ${conf}_problems.csv;
    
  done;
rm temp.txt
echo "Results are in ${conf}_problems.csv";
