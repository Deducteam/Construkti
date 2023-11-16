# Double negation translation for higher-order Lambdapi proofs

This tool applies Kuroda's negative translation to Lambapi proofs written using natural deduction.

## Requirements

The input proofs require to only use the connectors and quantifiers presented in `logic.lp`, and the natural deduction rules presented in `deduction.lp`. 

## How to use it?

If you want to translate the proofs of `file.lp`, run `bash translate.sh file`. If you want to translate the proofs and to obtain simpler proofs that use rewrite rules, run `bash translate_rules.sh file`.

You can test it on the file `test`.

## How does it work?

`kuroda.lp` defines Kuroda's translation, i.e. the insertion of double negation before each formula and after each universal quantifier. Kuroda's translation relies on some properties, proved in `properties.lp`. The files `kuroda_rules.lp` and `properties_rules.lp` make use of `rules.lp`, which defines few rewrit rules that simplify the proofs.

`example.lp` presents few examples of proofs with their translation.