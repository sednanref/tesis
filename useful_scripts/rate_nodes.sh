#!/bin/bash

#This script must be in the results/partial_encoding/search directory
#of the fast-downward directory.

#To us this script just invoke it with two different configurations.
#Example: sh rate_nodes.sh dr.1.1.2.1800.cplex flow.20.1800.cplex

CONF1=$1;
CONF2=$2;
OUTPUT_FILE=rate_nodes_${CONF1}_${CONF2}.csv;

echo "" > $OUTPUT_FILE;
#Search for the problems...
for PROB in ${CONF1}/*; do
  #Search for the instances...
  for INS in ${PROB}/*; do
    #Look if the solution has been found.
    CONF1_SOLVED=`grep "^Solution found." ${INS}/search_log | wc -l`;
    #If CONF1 has not solved it...
    if [ $CONF1_SOLVED = 0 ]; then
      #Take the instance path without the CONF1 configuration.
      G_INS=`echo ${INS} | cut -d/ -f2,3`;
      #Use that path to search that instance in the CONF2 configuration.
      CONF2_INS=`echo ${CONF2}/${G_INS}`;
      #Look if CONF2 hasn't solved it.
      CONF2_SOLVED=`grep "^Solution found." ${CONF2_INS}/search_log | wc -l`;
      #If CONF2 hasn't solved it...
      if [ $CONF2_SOLVED = 0 ]; then
        #Look if exists at least one "Best heuristic value" in both configurations
        EXISTS_CONF1_BV=`grep "^Best heuristic" ${INS}/search_log | wc -l`;
        EXISTS_CONF2_BV=`grep "^Best heuristic" ${CONF2_INS}/search_log | wc -l`;
        #If exists thos values...
        if [ "$EXISTS_CONF1_BV" -ne 0 ] && [ "$EXISTS_CONF2_BV" -ne 0 ]; then
            #Look for the last best heuristic value taken by CONF1
            CONF1_EXP=`grep "^Best heuristic" ${INS}/search_log | tail -1 | awk '{print $8}'`;
            #Look for the last best heuristic value taken by CONF2
            CONF2_EXP=`grep "^Best heuristic" ${CONF2_INS}/search_log | tail -1 | awk '{print $8}'`;

            CONF1_TIME=`grep "^Best heuristic" ${INS}/search_log | tail -1 | cut -d'=' -f3 | cut -ds -f1`;

            CONF2_TIME=`grep "^Best heuristic" ${CONF2_INS}/search_log | tail -1 | cut -d'=' -f3 | cut -ds -f1`;

            CONF1_V=`echo $CONF1_EXP $CONF1_TIME | awk '{printf "%.5f", $1/$2}'`;
            
            CONF2_V=`echo $CONF2_EXP $CONF2_TIME | awk '{printf "%.5f", $1/$2}'`;


            CONF2_TIMES_CONF1=`echo $CONF2_V $CONF1_V | awk '{printf "%.5f", $1/$2}'`;

            #Write those values in the output file
            echo  ${G_INS},${CONF1_V},${CONF2_V},${CONF2_TIMES_CONF1} >> $OUTPUT_FILE;
        fi;
      fi;
    fi;
  done;
done;

echo "Results are in ${OUTPUT_FILE}";
