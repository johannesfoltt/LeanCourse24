# A formalization of Lawvere's fixed point theorem

## Main results

The main body of this project is made up of different versions of [Lawvere's fixed point theorem](https://ncatlab.org/nlab/show/Lawvere's+fixed+point+theorem) (LFPT):

* The standard theorem for Cartesian closed categories
* The weaker version for point-surjective morphisms instead of weakly point-surjective morphisms
* The "uncurried" version for categories with only finite products
* A non-categorical version formulated only in terms of types

Using the type-theoretic version of LFPT additionally prove Cantor's theorem.

## Unfinished/unsuccessful formalization

After finishing the proofs of LFPT, I attempted to formalize two of its cosequences, namely:

* Cantor's theorem in a topos (cf. Prop. 2.4 [here](https://ncatlab.org/nlab/show/Lawvere's+fixed+point+theorem))
* [Lawvere's proof](http://tac.mta.ca/tac/reprints/articles/15/tr15.pdf) of Tarski's undefinability theorem

I couldn't formalize Cantor's theorem in a topos, because its proof depends on the existence of pushouts in topoi. This was pointed out to me by [Charlie Colleen](https://github.com/CharredLee), author of [this](https://github.com/CharredLee/topos) GitHub repository on topos theory.

Lawvere's proof of Tarski's undefinability theorem did not work, because I could not properly define the "Lindenbaum category" described by Lawvere [in this paper](http://tac.mta.ca/tac/reprints/articles/15/tr15.pdf). In essence we want to assign a morphism to every L-term and L-formula for some language L. However, the type of these morphisms depends on the terms and formulas, which makes it really difficult to compare them.

## Sources

* William Lawvere, Diagonal Arguments and Cartesian Closed Categories, Lecture Notes in Mathematics, 92 (1969) 134-145 [source](http://tac.mta.ca/tac/reprints/articles/15/tr15.pdf)

* nLab Article "Lawvere's fixed point theorem" [source](https://ncatlab.org/nlab/show/Lawvere's+fixed+point+theorem)