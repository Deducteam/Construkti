# Construkti, a double negation translator for higher-order proofs in Dedukti

[Dedukti](https://github.com/Deducteam/Dedukti) is a proof language based on the λΠ-calculus modulo theory, that is λ-calculus with dependent types and user-defined rewrite rules.

Kuroda's translation adds double negations in front of each formulas and after each universal quanftifiers. A formula admits a classical proofs if and only if its Kuroda's translation admits an intuitionistic proof.

This tool applies Kuroda's translation to Dedukti proofs written using natural deduction. It takes as input classical proofs, and returns the intuitionistic proofs of the translated theorems.


## Requirements

- Opam and OCaml

- Install [Dedukti](https://github.com/Deducteam/Dedukti?tab=readme-ov-file#install-with-opam) with Opam.


## How to use it?

- Clone this repository:
```
git clone https://github.com/thomastraversie/construkti/
```

- Enter this repository:
```
cd construkti
```

- Write your proofs only using the connectors, quantifiers, and natural deduction rules presented in `logic.dk`. If you want to translate the Dedukti file `file.dk` such that the concatenation of `logic.dk` and `file.dk` typechecks, run 
```
bash translate.sh file.dk
```
The translated proofs are displayed in the file `file_c.dk`.


## Benchmark

You can test Construkti on `hol-lib.dk`. This library contains the proofs of 100 theorems 
- in propositional, first-order and higher-order logics
- including classical theorems
- about logical connectives, equality and basic arithmetic
- using Dedukti features such as user-defined rewrite rules. 

After translation, `hol-lib_c.dk` only contains intuitionistic proofs.
