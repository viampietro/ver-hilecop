#!/bin/bash

usage()
{
cat << EOF
usage: ./gen_coqp [-h|--help] [-wp|--without-proof]
-p | --proof  Include files related to the proof in the _CoqProject file
-h | --help   Display this message
EOF
}

# Regex pointing out the proof-related files in the VerHilecop
# project.

PROOF_FILES_PATTERN="\(.*/proofs/.*\|.*/behavior-preservation/.*\)"

# Files to be excluded from the _CoqProject file.
EXCLUDED_FILES_PATTERN="\(./hvhdl/SynchronousEvaluation.v\|./hvhdl/CombinationalEvaluation.v\)"

# Parsing the command options.

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

# Saving the _CoqProject file if exists.

if [ -e _CoqProject ]; then
    echo "Saving old _CoqProject file to _CoqProject.copy"
    mv _CoqProject _CoqProject.copy
fi

# Mapping physical directory to logical Coq directory through the "-R"
# option, and adds the mappings to the _CoqProject file.

echo "-R common/ hilecop.common
-R sitpn/ hilecop.sitpn
-R hvhdl/ hilecop.hvhdl
-R transformation/ hilecop.transformation
-R behavior-preservation/ hilecop.soundness" > _CoqProject

# Displays all the Vernacular files (.v) of the project and adds them
# in the _CoqProject file.

# Filters out all files matching the EXCLUDED_FILES_PATTERN pattern,
# the PROOF_FILES_PATTERN pattern, the "./common/DFMapWeakList.v" or
# file names beginning with a dot.

# Do not add to _CoqProject the files under the "test" folder.
find . -name *.v -type f ! -regex "$PROOF_FILES_PATTERN" \
     ! -regex ".*/\..+" \
     ! -regex "$EXCLUDED_FILES_PATTERN" \
     ! -regex ".*/test/.*" >> _CoqProject



