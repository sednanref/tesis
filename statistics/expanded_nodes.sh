#!/bin/bash

#This script must be in the results/partial_encoding/search directory
#of the fast-downward directory.

#This script returns the expanded nodes provided till the last f-layer (excluding it) of a heuristic evaluation for solved problems on each configuration provided to the script.

#To us this script just invoke it with two different configurations.
#Example: sh expanded_nodes.sh dr.1.1.2.1800.cplex flow.20.1800.cplex

CONF1=$1;
CONF2=$2;
OUTPUT_FILE=expanded_nodes_${CONF1}_${CONF2}.csv;

echo "" > $OUTPUT_FILE;
#Search for the problems...
for PROB in ${CONF1}/*; do
  #Search for the instances...
  for INS in ${PROB}/*; do
    #Look if the solution has been found.
    CONF1_SOLVED=`grep "^Solution found." ${INS}/search_log | wc -l`;
    #If CONF1 has solved it...
    if [ $CONF1_SOLVED -ne 0 ]; then
      #Take the instance path without the CONF1 configuration.
      G_INS=`echo ${INS} | cut -d/ -f2,3`;
      #Use that path to search that instance in the CONF2 configuration.
      CONF2_INS=`echo ${CONF2}/${G_INS}`;
      #Look if CONF2 hasn't solved it.
      CONF2_SOLVED=`grep "^Solution found." ${CONF2_INS}/search_log | wc -l`;
      #If CONF2 has solved it...
      if [ $CONF2_SOLVED -ne 0 ]; then
        #Look for the expanded nodes value taken by CONF1
        CONF1_EXP=`grep "^Expanded until last" ${INS}/search_log | awk '{print $5}'`;
        #Look for the expanded nodes value taken by CONF2
        CONF2_EXP=`grep "^Expanded until last" ${CONF2_INS}/search_log | awk '{print $5}'`;
        #Write those values in the output file
        echo ${G_INS},${CONF1_EXP},${CONF2_EXP} >> $OUTPUT_FILE;
      else
        #Look if exists at least one "Best heuristic value" in both configurations
        CONF1_EXP=`grep "^Expanded until last" ${INS}/search_log | awk '{print $5}'`;          
        echo ${G_INS},${CONF1_EXP}, >> $OUTPUT_FILE;
      fi;
    #If both first configuration did not resolve the instance.
    else
      #Take the instance path without the CONF1 configuration.
      G_INS=`echo ${INS} | cut -d/ -f2,3`;
      #Use that path to search that instance in the CONF2 configuration.
      CONF2_INS=`echo ${CONF2}/${G_INS}`;
      #Look if CONF2 hasn't solved it.
      CONF2_SOLVED=`grep "^Solution found." ${CONF2_INS}/search_log | wc -l`;
      #If the second configuration did resolve the instance...
      if [ $CONF2_SOLVED -ne 0 ]; then
          #Look for the last expanded nodes taken by CONF2
          CONF2_EXP=`grep "^Expanded until last" ${CONF2_INS}/search_log | awk '{print $5}'`;
          #Write it to the file.
          echo  ${G_INS},,${CONF2_EXP} >> $OUTPUT_FILE;
      #If both configurations didn't found a solution...
      else
          #Write thos "null" values to the file.
          echo ${G_INS},, >> ${OUTPUT_FILE};
      fi;
    fi;
  done;
done;

echo "Results are in ${OUTPUT_FILE}";
