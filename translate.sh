#!/bin/bash

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
sed -i 's/fa_i /fa_i_c /g' ./$1_c/*.lp
sed -i 's/fa_e /fa_e_c /g' ./$1_c/*.lp
sed -i 's/ex_i /ex_i_c /g' ./$1_c/*.lp
sed -i 's/ex_e /ex_e_c /g' ./$1_c/*.lp
sed -i 's/absurd /absurd_c /g' ./$1_c/*.lp

sed -i 's/apply /refine /g' ./$1_c/*.lp

sed -i '1s/^/require open Construkti.properties;\nrequire open Construkti.kuroda;\n/' ./$1_c/*.lp

sed -i "s/Construkti.$1/Construkti.$1_c/g" ./$1_c/*.lp

echo "Files translated"