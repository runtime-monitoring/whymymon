#!/bin/bash

# Input parameters:
SIZE=$2
ER=$3
DELTA=$4
SEED=$5

# Flags:
CHECK_FLAG=$1

# Variables:
PREFIX="TMP_${SIZE}_${ER}_${DELTA}_${SEED}"
OUT=""

usage () {
    printf "usage: test_seed.sh [verified or unverified] [size] [er] [delta] [seed]\n"
    exit 1
}

verb () {

    python test/fo_gen/gen_for.py -pred 5 -A 5 -S ${SIZE} -seed ${SEED} -out test/fo_gen/tmp/${PREFIX} -prob_let 0 -prob_rand 0 -prob_eand 0 -prob_nand 0 > /dev/null

    python test/fo_gen/gen_log.py -sig test/fo_gen/tmp/${PREFIX}.sig -form test/fo_gen/tmp/${PREFIX}.mfotl -i ${DELTA} -e ${ER} -l 500 -log test/fo_gen/tmp/${PREFIX} -logseed ${SEED} > /dev/null

    if [[ "${CHECK_FLAG}" = "verified" ]]
    then
        OUT=$(bin/whymymon.exe -path default -cli -mode verified -pref sat -sig test/fo_gen/tmp/${PREFIX}.sig -formula test/fo_gen/tmp/${PREFIX}.mfotl -log test/fo_gen/tmp/${PREFIX}.log 2>&1)
    else
        if [[ "${CHECK_FLAG}" = "unverified" ]]
        then
            OUT=$(bin/whymymon.exe -path default -cli -mode unverified -pref sat -sig test/fo_gen/tmp/${PREFIX}.sig -formula test/fo_gen/tmp/${PREFIX}.mfotl -log test/fo_gen/tmp/${PREFIX}.log 2>&1)
        else
            usage
        fi
    fi

    OUT_GREP=$(grep "Checker output: false\|exception" <<< "${OUT}")

    printf "${PREFIX} ... "
    if [[ "${OUT_GREP}" == "" ]]
    then
        printf "OK\n"
    fi
    if [[ "${OUT_GREP}" == *"false"* ]]
    then
        printf " !! CHECK FAILED !!\n"
    fi
    if [[ "${OUT_GREP}" == *"exception"* ]]
    then
        printf " !! EXCEPTION RAISED !!\n"
        printf "${OUT}\n"
    fi
    printf "\n"
}

if [ "$#" -eq 5 ]
then
    time verb
else
    usage
fi
