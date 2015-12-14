#!/bin/bash

#This script must be in the results/partial_encoding/search directory
#of the fast-downward directory.

#To us this script just invoke it with two different configurations.
#Example: sh conf1_vs_conf2.sh dr.1.1.2.1800.cplex flow.20.1800.cplex

CONF1=$1;
CONF2=$2;
OUTPUT_FILE=${CONF1}_${CONF2}.csv;

echo "" > $OUTPUT_FILE;
#Search for the problems...
for PROB in ${CONF1}/*; do
  #Search for the instances...
  for INS in ${PROB}/*; do
    #Look if the solution has been found.
    CONF1_SOLVED=`grep "^Solution found." ${INS}/search_log | wc -l`;
    #If conf1 has not solved it...
    if [ $CONF1_SOLVED = 0 ]; then
      #Take the instance path without the DR configuration.
      G_INS=`echo ${INS} | cut -d/ -f2,3`;
      #Use that path to search that instance in the conf2.
      CONF2_INS=`echo ${CONF2}/${G_INS}`;
      #Look if CONF2 hasn't solved it.
      CONF2_SOLVED=`grep "^Solution found." ${CONF2_INS}/search_log | wc -l`;
      #If flow hasn't solved it...
      if [ $CONF2_SOLVED = 0 ]; then
        #Look if exists at least one "Best heuristic value" in both configurations
        EXISTS_CONF1_BV=`grep "^Best heuristic" ${INS}/search_log | wc -l`;
        EXISTS_CONF2_BV=`grep "^Best heuristic" ${CONF2_INS}/search_log | wc -l`;
        #If exists thos values...
        if [ "$EXISTS_CONF1_BV" -ne 0 ] && [ "$EXISTS_CONF2_BV" -ne 0 ]; then
            #Look for the last best heuristic value taken by DR
            CONF1_BV=`grep "^Best heuristic" ${INS}/search_log | tail -1 | awk '{print $4}'`;
            #Look for the last best heuristic value taken by flow
            CONF2_BV=`grep "^Best heuristic" ${CONF2_INS}/search_log | tail -1 | awk '{print $4}'`;
            #Write those values in the output file
            echo -n ${G_INS},${CONF1_BV},${CONF2_BV}, >> $OUTPUT_FILE;
            #if the last best heuristic value of DR is less than the best
            #heuristic value of flow...
            if [ "$CONF1_BV" -lt "$CONF2_BV" ]; then
              #put a 1 value in the output file.
              echo yes >> $OUTPUT_FILE;
            else
              #else put a 0 value in the output file
              echo no >> $OUTPUT_FILE;
            fi;
        fi;
      fi;
    fi;
  done;
done;

echo "Results are in ${OUTPUT_FILE}";
