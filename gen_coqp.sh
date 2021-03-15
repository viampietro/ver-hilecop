#!/bin/bash

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

find -name *.v ! -path "./*/\.*" ! -path "./common/DFMapWeakList.v" >> _CoqProject
