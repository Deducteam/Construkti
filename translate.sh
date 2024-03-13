#!/bin/bash

extension="${1##*.}"
filename="${1%.*}"

GREEN='\033[0;32m'
RED='\033[0;31m'
NOCOLOR='\033[0m'

if [ $extension = "dk" ]
then
    new="${filename}_c.dk"
    tmp="tmp.dk"
    tmp2="tmp2.dk"
    cp -r $1 $tmp

    sed -i 's/Prf /Prf_c /g' $tmp
    sed -i 's/Prf(/Prf_c(/g' $tmp
    sed -i 's/all /all_c /g' $tmp
    sed -i 's/imp_i /imp_i_c /g' $tmp
    sed -i 's/imp_e /imp_e_c /g' $tmp
    sed -i 's/and_i /and_i_c /g' $tmp
    sed -i 's/and_el /and_el_c /g' $tmp
    sed -i 's/and_er /and_er_c /g' $tmp
    sed -i 's/or_il /or_il_c /g' $tmp
    sed -i 's/or_ir /or_ir_c /g' $tmp
    sed -i 's/or_e /or_e_c /g' $tmp
    sed -i 's/neg_i /neg_i_c /g' $tmp
    sed -i 's/neg_e /neg_e_c /g' $tmp
    sed -i 's/top_i/top_i_c/g' $tmp
    sed -i 's/bot_e /bot_e_c /g' $tmp
    sed -i 's/all_i /all_i_c /g' $tmp
    sed -i 's/all_e /all_e_c /g' $tmp
    sed -i 's/ex_i /ex_i_c /g' $tmp
    sed -i 's/ex_e /ex_e_c /g' $tmp
    sed -i 's/excluded_middle /excluded_middle_c /g' $tmp

    dune build
    dune exec -- construkti --file $tmp > $tmp2
    sed -i 's/{ //g' $tmp2
    sed -i 's/ }//g' $tmp2
    sed -i 's/tmp.//g' $tmp2
    dk beautify $tmp2 > $tmp

    cat kuroda.dk $tmp > $new
    rm $tmp $tmp2
    
    echo -e "${GREEN}[SUCCESS]${NOCOLOR} $1 was successfully translated into $new."
    dk check $new

else
    echo -e "${RED}[ERROR]${NOCOLOR} $1 is not a Dedukti file."
fi
