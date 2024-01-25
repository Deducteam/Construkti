#!/bin/bash

extension="${1##*.}"
filename="${1%.*}"


if [ $extension = "lp" ]
then
    new="${filename}_c.lp"
    cp -r $1 $new

    sed -i 's/ Prf/ Prf ¬ ¬/g' $new
    sed -i 's/∀/∀_c/g' $new
    sed -i 's/imp_i /imp_i_c /g' $new
    sed -i 's/imp_e /imp_e_c /g' $new
    sed -i 's/and_i /and_i_c /g' $new
    sed -i 's/and_e_l /and_e_l_c /g' $new
    sed -i 's/and_e_r /and_e_r_c /g' $new
    sed -i 's/or_i_r /or_i_r_c /g' $new
    sed -i 's/or_i_l /or_i_l_c /g' $new
    sed -i 's/or_e /or_e_c /g' $new
    sed -i 's/neg_i /neg_i_c /g' $new
    sed -i 's/neg_e /neg_e_c /g' $new
    sed -i 's/top_i/top_i_c/g' $new
    sed -i 's/bot_e /bot_e_c /g' $new
    sed -i 's/all_i /all_i_c /g' $new
    sed -i 's/all_e /all_e_c /g' $new
    sed -i 's/ex_i /ex_i_c /g' $new
    sed -i 's/ex_e /ex_e_c /g' $new
    sed -i 's/absurd /absurd_c /g' $new
    sed -i 's/apply /refine /g' $new
    sed -i '1s/^/require open Construkti.properties;\nrequire open Construkti.kuroda;\n/' $new

    echo "$1 has been translated"


elif [ $extension = "dk" ]
then
    new="${filename}_c.dk"
    tmp="tmp.dk"
    cp -r $1 $tmp

    sed -i 's/ Prf/ Prf_c/g' $tmp
    sed -i 's/all/all_c/g' $tmp
    sed -i 's/imp_i /imp_i_c /g' $tmp
    sed -i 's/imp_e /imp_e_c /g' $tmp
    sed -i 's/and_i /and_i_c /g' $tmp
    sed -i 's/and_e_l /and_e_l_c /g' $tmp
    sed -i 's/and_e_r /and_e_r_c /g' $tmp
    sed -i 's/or_i_r /or_i_r_c /g' $tmp
    sed -i 's/or_i_l /or_i_l_c /g' $tmp
    sed -i 's/or_e /or_e_c /g' $tmp
    sed -i 's/neg_i /neg_i_c /g' $tmp
    sed -i 's/neg_e /neg_e_c /g' $tmp
    sed -i 's/top_i/top_i_c/g' $tmp
    sed -i 's/bot_e /bot_e_c /g' $tmp
    sed -i 's/all_i /all_i_c /g' $tmp
    sed -i 's/all_e /all_e_c /g' $tmp
    sed -i 's/ex_i /ex_i_c /g' $tmp
    sed -i 's/ex_e /ex_e_c /g' $tmp
    sed -i 's/absurd /absurd_c /g' $tmp

    cat logic.dk properties.dk kuroda.dk $tmp > $new
    rm $tmp
    echo "$1 has been translated"


else
    cp -r $1 $1_c

    sed -i 's/ Prf/ Prf ¬ ¬/g' ./$1_c/*.lp
    sed -i 's/∀/∀_c/g' ./$1_c/*.lp
    sed -i 's/imp_i /imp_i_c /g' ./$1_c/*.lp
    sed -i 's/imp_e /imp_e_c /g' ./$1_c/*.lp
    sed -i 's/and_i /and_i_c /g' ./$1_c/*.lp
    sed -i 's/and_e_l /and_e_l_c /g' ./$1_c/*.lp
    sed -i 's/and_e_r /and_e_r_c /g' ./$1_c/*.lp
    sed -i 's/or_i_r /or_i_r_c /g' ./$1_c/*.lp
    sed -i 's/or_i_l /or_i_l_c /g' ./$1_c/*.lp
    sed -i 's/or_e /or_e_c /g' ./$1_c/*.lp
    sed -i 's/neg_i /neg_i_c /g' ./$1_c/*.lp
    sed -i 's/neg_e /neg_e_c /g' ./$1_c/*.lp
    sed -i 's/top_i/top_i_c/g' ./$1_c/*.lp
    sed -i 's/bot_e /bot_e_c /g' ./$1_c/*.lp
    sed -i 's/all_i /all_i_c /g' ./$1_c/*.lp
    sed -i 's/all_e /all_e_c /g' ./$1_c/*.lp
    sed -i 's/ex_i /ex_i_c /g' ./$1_c/*.lp
    sed -i 's/ex_e /ex_e_c /g' ./$1_c/*.lp
    sed -i 's/absurd /absurd_c /g' ./$1_c/*.lp

    sed -i 's/apply /refine /g' ./$1_c/*.lp

    sed -i '1s/^/require open Construkti.properties;\nrequire open Construkti.kuroda;\n/' ./$1_c/*.lp

    sed -i "s/Construkti.$1/Construkti.$1_c/g" ./$1_c/*.lp

    for file in $1/*.lp
    do
        echo "$file has been translated"
    done

    echo "The translated files are in the folder $1_c"
    
fi
