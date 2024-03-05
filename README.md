# Construkti, a double negation translator for higher-order proofs in Dedukti and Lambdapi

[Dedukti](https://github.com/Deducteam/Dedukti) is a proof language based on the λΠ-calculus modulo theory, that is λ-calculus with dependent types and user-defined rewrite rules.

[Lambdapi](https://github.com/Deducteam/lambdapi) is a proof assitant based on the λΠ-calculus modulo theory, which can check and output Dedukti proofs.

Kuroda's translation adds double negations in front of each formulas and after each universal quanftifiers. A formula admits a classical proofs if and only if the translated formula admits an intuitionistic proof.

This tool applies Kuroda's translation to Dedukti/Lambapi proofs written using natural deduction. It takes as input classical proofs, and returns the intuitionistic proofs of the translated theorems.


## Requirements

- Install [Lambdapi](https://github.com/Deducteam/lambdapi) or [Dedukti](https://github.com/Deducteam/Dedukti).

- Clone this repository:
```
git clone https://github.com/thomastraversie/construkti/
```


## How to use it?

- Enter this repository:
```
cd construkti
```

- Write your proofs only using the connectors, quantifiers, and natural deduction rules presented in `logic.lp` or `logic.dk`. 



#### Dedukti file

If you want to translate the Dedukti file `file.dk` such that the concatenation of `logic.dk` and `file.dk` typechecks, run 
```
bash translate.sh file.dk
```
The translated proofs are displayed in the file `file_c.dk`.



#### Lambdapi file

If you want to translate the Lambdapi file `file.lp` that depends on the module `Construkti.logic`, run 
```
bash translate.sh file.lp
```
The translated proofs are displayed in the file `file_c.lp`.



#### Multiple Lambdapi files

If you want to translate all the Lambdapi files of the folder `folder`, run 
```
bash translate.sh folder
```
The translated files are displayed in the folder `folder_c`.


### Benchmark

You can test Construkti on `hol-lib.dk` and `hol-lib.lp`, that contain the proofs of theorems in propositional, first-order and higher-order logics, including classical theorems. After translation, `hol-lib_c.dk` and `hol-lib_c.lp` only contain intuitionistic proofs.