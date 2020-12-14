# Cusppairs
This package adds functionality to Jean Michel's development version
of [CHEVIE](https://github.com/jmichel7/gap3-jm) for calculating with
d-cuspidal pairs. The file provides the following functionality:

*   Ability to calculate the smallest split Levi subgroup of the parent
    of a Coxeter coset that contains that coset.
*   List all the Levi subgroups of a Coxeter coset that support a
    cuspidal unipotent character.

We note that this second feature is already available in CHEVIE but the
approach used here speeds things up by using the classification. More
details and examples of usage of the relevant functions can be found in
the header of the file cusppairs.g.
