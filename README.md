# Double negation translation for higher-order Lambdapi proofs

The input proofs require to only use the connectors and quantifiers presented in `logic.lp`, and the natural deduction rules presented in `deduction.lp`. 

`rules.lp` defines few rewrite rules that simplify the proofs. 

`kuroda_rules.lp` defines Kuroda's translation, i.e. the insertion of double negation before each formula and after each universal quantifier. Kuroda's translation relies on some properties, proved in `properties_rules.lp`. Both files make use of `rules.lp`.

`example.lp` presents few examples of proofs with their translation.