# NFA minimization using preorder and strongly connected components on dependency graphs
Here algorithms for preorders calculation and usage are presented,
along with a suite for testing and comparing results with minimization
approaches based on equivalences.

## Minimization algorithms
The minimization algorithm provided are:
* For equivalences:
    * `right_eq`: for minimization using only right equivalences
    * `right_left_eq`: for minimization using right and then left
    equivalences
* For preorders:
    * `preorders_with_sccs`: for minimization using SCC merging on 3
    dependency graphs
    * `preorders_with_sccs_right`: as above, but priority is given to
    SCCs found in the dependency graph associated to right preorders
    (so, for states that can be merged using rule 1 of states merging
    rules using preorders)
    * `preorders_with_sccs_left`: as above, but priority is given to
    rule 2
    * `preorders_with_sccs_pre`: as above, but priority is given to
    rule 3

#### NOTE
Left and left-right equivalences can be used in minimization
algorithms, by simply providing the reversed automaton and the
correct relations.

## Test
Mixed tests can be found into `tests` folder, while multiple batches
can be found into `TESTS`. Each batch is distinguished from the others
based on the length of the regular expression used for generating
each NFA and on vocabulary size.

New tests can be generated using `generate_example.py` script and
providing as argument: output folder, number of NFAs of each batch
and vocabulary size.