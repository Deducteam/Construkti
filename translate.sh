#!/bin/bash

extension="${1##*.}"
filename="${1%.*}"

if [ $extension = "dk" ]
then
    new="${filename}_c.dk"
    tmp="tmp.dk"
    tmp2="tmp2"
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

    cat kuroda.dk $tmp > "${tmp2}.dk"
    rm $tmp
    echo "[p] ${tmp2}.Prf_c p --> ${tmp2}.Prf (${tmp2}.not (${tmp2}.not p)). 
          [a, p] ${tmp2}.all_c a p --> ${tmp2}.all a (x : (${tmp2}.El a) => (${tmp2}.not (${tmp2}.not (p x))))." > meta.dk
    dk check -e "${tmp2}.dk" meta.dk
    dk meta -m meta.dk "${tmp2}.dk" > $new
    rm meta.dk meta.dko "${tmp2}.dk" "${tmp2}.dko"
    sed -i '/def Prf_c : Prop -> Type./d' $new
    sed -i '/Prf_c p --> Prf (not (not p))./d' $new
    sed -i '/def all_c : a:Set -> ((El a) -> Prop) -> Prop./d' $new
    sed -i '/all_c a p --> all a (x:(El a) => not (not (p x)))./d' $new
    echo "$1 has been translated"


elif [ $extension = "lp" ]
then
    new="${filename}_c.lp"
    cp -r $1 $new

    sed -i 's/Prf /Prf ¬ ¬ /g' $new
    sed -i 's/Prf(/Prf ¬ ¬(/g' $new
    sed -i 's/∀/∀_c/g' $new
    sed -i 's/imp_i /imp_i_c /g' $new
    sed -i 's/imp_e /imp_e_c /g' $new
    sed -i 's/and_i /and_i_c /g' $new
    sed -i 's/and_el /and_el_c /g' $new
    sed -i 's/and_er /and_er_c /g' $new
    sed -i 's/or_il /or_il_c /g' $new
    sed -i 's/or_ir /or_ir_c /g' $new
    sed -i 's/or_e /or_e_c /g' $new
    sed -i 's/neg_i /neg_i_c /g' $new
    sed -i 's/neg_e /neg_e_c /g' $new
    sed -i 's/top_i/top_i_c/g' $new
    sed -i 's/bot_e /bot_e_c /g' $new
    sed -i 's/all_i /all_i_c /g' $new
    sed -i 's/all_e /all_e_c /g' $new
    sed -i 's/ex_i /ex_i_c /g' $new
    sed -i 's/ex_e /ex_e_c /g' $new
    sed -i 's/excluded_middle /excluded_middle_c /g' $new
    sed -i 's/apply /refine /g' $new
    sed -i '1s/^/require open Construkti.properties;\nrequire open Construkti.kuroda;\n/' $new

    echo "$1 has been translated"


else
    cp -r $1 $1_c

    sed -i 's/Prf /Prf ¬ ¬ /g' ./$1_c/*.lp
    sed -i 's/Prf(/Prf ¬ ¬(/g' ./$1_c/*.lp
    sed -i 's/∀/∀_c/g' ./$1_c/*.lp
    sed -i 's/imp_i /imp_i_c /g' ./$1_c/*.lp
    sed -i 's/imp_e /imp_e_c /g' ./$1_c/*.lp
    sed -i 's/and_i /and_i_c /g' ./$1_c/*.lp
    sed -i 's/and_el /and_el_c /g' ./$1_c/*.lp
    sed -i 's/and_er /and_er_c /g' ./$1_c/*.lp
    sed -i 's/or_il /or_il_c /g' ./$1_c/*.lp
    sed -i 's/or_ir /or_ir_c /g' ./$1_c/*.lp
    sed -i 's/or_e /or_e_c /g' ./$1_c/*.lp
    sed -i 's/neg_i /neg_i_c /g' ./$1_c/*.lp
    sed -i 's/neg_e /neg_e_c /g' ./$1_c/*.lp
    sed -i 's/top_i/top_i_c/g' ./$1_c/*.lp
    sed -i 's/bot_e /bot_e_c /g' ./$1_c/*.lp
    sed -i 's/all_i /all_i_c /g' ./$1_c/*.lp
    sed -i 's/all_e /all_e_c /g' ./$1_c/*.lp
    sed -i 's/ex_i /ex_i_c /g' ./$1_c/*.lp
    sed -i 's/ex_e /ex_e_c /g' ./$1_c/*.lp
    sed -i 's/excluded_middle /excluded_middle_c /g' ./$1_c/*.lp

    sed -i 's/apply /refine /g' ./$1_c/*.lp

    sed -i '1s/^/require open Construkti.properties;\nrequire open Construkti.kuroda;\n/' ./$1_c/*.lp

    sed -i "s/Construkti.$1/Construkti.$1_c/g" ./$1_c/*.lp

    for file in $1/*.lp
    do
        echo "$file has been translated"
    done

    echo "The translated files are in the folder $1_c"
    
fi
