#!/bin/bash

usage()
{
cat << EOF
usage: ./gen_coqp [-h|--help] [-wp|--without-proof]
-p | --proof  Include files related to the proof in the _CoqProject file
-h | --help   Display this message
EOF
}

PROOF_FILES_PATTERN="\(.*/proofs/.*\|.*/soundness/.*\)"

while [ "$1" != "" ]; do
    case $1 in
        -p | --proof )
            shift
	    PROOF_FILES_PATTERN=""
            ;;
        -h | --help )
	    usage
	    exit
	    ;;
	
        * )
	    usage
	    exit
	    ;;
    esac
    shift
done

if [ -e _CoqProject ]; then
    echo "Saving old _CoqProject file to _CoqProject.copy"
    mv _CoqProject _CoqProject.copy
fi

echo "-R common/ hilecop.common
-R sitpn/ hilecop.sitpn
-R hvhdl/ hilecop.hvhdl
-R sitpn2hvhdl/ hilecop.sitpn2hvhdl
-R soundness/ hilecop.soundness
-R test/ hilecop.test" > _CoqProject

find . -name *.v -type f ! -regex "$PROOF_FILES_PATTERN" ! -regex ".*/\..+" ! -regex "./common/DFMapWeakList.v" >> _CoqProject



