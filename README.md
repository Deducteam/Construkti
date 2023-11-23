# Double negation translation for higher-order Lambdapi proofs

[Lambdapi](https://github.com/Deducteam/lambdapi) is a proof assitant based on the λΠ-calculus modulo, that is λ-calculus with dependent types and user-defined rewrite rules. It is a logical framework in which you can express different theories.

Kuroda's translation adds double negations in front of each formulas and after each universal quanftifiers. A formula admits a classical proofs if and only if the translated formula admits an intuitionistic proof.

This tool applies Kuroda's translation to Lambapi proofs written using natural deduction. It takes as input classical proofs, and returns the intuitionistic proofs of the translated theorems.


## How to use it?

- Install [Lambdapi](https://github.com/Deducteam/lambdapi).

- Clone this repository:
```
git clone https://github.com/thomastraversie/construkti/
cd construkti
```
- Write your proofs only using the connectors and quantifiers presented in `logic.lp`, and the natural deduction rules presented in `deduction.lp`. 

- If you want to translate the proofs of `file.lp`, run 
```
bash translate.sh file
```

NB: If you want to translate the proofs and to obtain simpler proofs that use rewrite rules, run 
```
bash translate_rules.sh file
```
You can test it on the file `test.lp`.


## How does it work?

`kuroda.lp` defines Kuroda's translation, i.e. the insertion of double negation before each formula and after each universal quantifier. Kuroda's translation relies on some properties, proved in `properties.lp`. The files `kuroda_rules.lp` and `properties_rules.lp` make use of `rules.lp`, which defines few rewrite rules that simplify the proofs.