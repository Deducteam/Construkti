# Construkti, a double negation translator for higher-order proofs in Dedukti and Lambdapi

[Dedukti](https://github.com/Deducteam/Dedukti) is a proof language based on the λΠ-calculus modulo, that is λ-calculus with dependent types and user-defined rewrite rules.

[Lambdapi](https://github.com/Deducteam/lambdapi) is a proof assitant based on the λΠ-calculus modulo, which can check and output Dedukti proofs.

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


#### Lambdapi file

If you want to translate the Lambdapi file `file.lp` that depends on the module `Construkti.logic`, run 
```
bash translate.sh file.lp
```
The translated proofs are displayed in the file `file_c.lp`. You can test it with `test.lp`.



#### Dedukti file

If you want to translate the Dedukti file `file.dk` such that the concatenation of `logic.dk` and `file.dk` typechecks, run 
```
bash translate.sh file.dk
```
The translated proofs are displayed in the file `file_c.dk`. You can test it with `test.dk`.



#### Multiple Lambdapi files

If you want to translate all the Lambdapi files of the folder `folder`, run 
```
bash translate.sh folder
```
The translated files are displayed in the folder `folder_c`.

You can test it on the folder `library`, that contain some proofs in higher-order logic.