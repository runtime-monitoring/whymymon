#!/bin/bash

## * gen_fmla
##
## PREFIX | SIZE | MAXR | TYPE | SCALE | SEED | APS
##                  10     0                    16
##
## * gen_log
## PREFIX | TS_CNT | ER | DELTA | SEED | APS
##           100                         16
##
## * possible combinations
## SIZE  -> 10 100
## SCALE -> 1  5   10
## ER    -> 1  10  100
## DELTA -> 4  100

# Script's full path
FULL_PATH=$(readlink -f -- "$0")
CUR_DIR=${FULL_PATH%/*}

# Input parameters:
N_SEEDS=$1

# Flags:
CHECK_FLAG=$2

usage () {
    printf "usage: run_tests.sh [n_seeds] [verified or unverified]\n"
    exit 1
}

if ! [[ "${N_SEEDS}" =~ ^[0-9]+$ ]] || ! [ "$#" -eq 2 ]
then
    usage
fi

# Arrays:
# SIZES=(10 20)
# SCALES=(1 5 10)
# ERS=(1 5 10)
# DELTAS=(4 8 12)
SIZES=(3 4 5 6 7 8 9 10)
SCALES=(1 5)
ERS=(1 5)
DELTAS=(4)
SEEDS=$(seq 0 "${N_SEEDS}")

for i in "${SIZES[@]}"; do
    for j in "${SCALES[@]}"; do
        for k in "${ERS[@]}"; do
            for l in "${DELTAS[@]}"; do
                if [[ "${CHECK_FLAG}" == "verified" ]]
                then
                    printf "<@> Running ${N_SEEDS} verified tests with parameters\n"
                    printf "<@> { size = $i | scale = $j | er = $k | delta = $l }\n"

                    time parallel ./test/test_seed.sh verified $i $j $k $l ::: "${SEEDS}"

                    # ./clean.sh
                    printf "\n"
                else
                    if [[ "${CHECK_FLAG}" == "unverified" ]]
                    then
                        printf "<@> Running ${N_SEEDS} tests with parameters\n"
                        printf "<@> { size = $i | scale = $j | er = $k | delta = $l }\n"

                        time parallel ./test/test_seed.sh unverified $i $j $k $l ::: "${SEEDS}"

                        # ./clean.sh
                        printf "\n"
                    else
                        usage
                    fi
                fi
            done
        done
    done
done
