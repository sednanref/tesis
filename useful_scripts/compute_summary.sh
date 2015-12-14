#!/bin/bash

versions=$*

# Extract basic data from experimental results
for ver in $versions; do
    cost_summary=SUMMARY.$ver.cost
    time_summary=SUMMARY.$ver.time
    (cd $ver; grep "Plan cost" */*/search_log) > $cost_summary
    (cd $ver; grep "Total time" */*/search_log) > $time_summary
    echo $ver: `cat $cost_summary | wc -l`
done

