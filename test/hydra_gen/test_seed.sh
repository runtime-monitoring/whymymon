#!/bin/bash

# ./test_seed.sh verified 10 1 1 4 144

# Input parameters:
SIZE=$2
SCALE=$3
ER=$4
DELTA=$5
SEED=$6

# Flags:
CHECK_FLAG=$1

# Variables:
PREFIX="TMP_${SIZE}_${SCALE}_${ER}_${DELTA}_${SEED}"
OUT=""

usage () {
    printf "usage: test_seed.sh [verified or unverified] [size] [scale] [er] [delta] [seed]\n"
    exit 1
}

verb () {

    ./test/gen_fmla ${PREFIX} ${SIZE} 10 0 ${SCALE} ${SEED} 16

    ./test/gen_log ${PREFIX} 100 ${ER} ${DELTA} ${SEED} 16

    mv ${PREFIX}.* test/tmp/

    if [[ "${CHECK_FLAG}" = "verified" ]]
    then
        OUT=$(../bin/whymymon.exe -path default -mode verified -sig sig/ap.sig -formula tmp/${PREFIX}.mfotl -log tmp/${PREFIX}.mlog 2>&1)
    else
        if [[ "${CHECK_FLAG}" = "unverified" ]]
        then
            OUT=$(../bin/whymymon.exe -path default -mode unverified -sig sig/ap.sig -formula tmp/${PREFIX}.mfotl -log tmp/${PREFIX}.mlog 2>&1)
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

if [ "$#" -eq 6 ]
then
    time verb
else
    usage
fi
