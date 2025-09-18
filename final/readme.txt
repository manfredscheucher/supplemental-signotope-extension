This repository contains supplemental material to the article 
"An extension theorem for signotopes"
by Helena Bergold, Stefan Felsner, and Manfred Scheucher

In the "examples" folder, we provide non-extendable examples for ranks 4, 6, 8, 10, and 12. 
The files are plain text format, each line encodes a signotope, 
and the symbols (either plus or minus) of a line 
encode the triple orientations in lexicographic order.

We also provide the source code for our program "test_extension.py" 
which tests the 2-extendability.
The following commands can be run to verify the examples:
    python test_extension.py 4 8 examples/x4 -EO -1
    python test_extension.py 6 12 examples/x6 -EO -1
    python test_extension.py 8 16 examples/x8 -EO -1
    python test_extension.py 10 20 examples/x10 -EO -1
    python test_extension.py 12 24 examples/x12 -EO -1

The first parameters specifies the rank~$r$, 
the second parameter specifies the number of elements~$n$ (in the examples we have $n=2r$).
and the third parameter specifies the input file where each line encodes a signotope.
The parameter \verb|-EO| is optional and restricts the program to only test the extendability for $(r-1)$-sets $I,J$ where $I$ only contains even and $J$ only contains odd indices.
The parameter \verb|-1| is optional and restricts the program to only test the extendability for one pair of $I,J$. 
Note that in our examples non-2-extendability is witnessed by all pairs $I,J$ 
where $I$ only contains even and $J$ only contains odd indices.
Using an Intel(R) Core(TM) i7-8700 CPU @ 3.20GHz (12 threads) with about 50 GB of RAM,
the examples in ranks 4,6,8 can be verified in about 30 CPU seconds, 
and for rank 10 in about 9 CPU hours. 
The verification for rank 12 takes several CPU months and uses about 50 GB of RAM.

For the interested reader, we also provide the programs
"find_signotopes.py", which we initially used to find the examples in rank 4,
and the program "find_signotopes_induction.py", which we used to iteratively
construct the examples in ranks 6, 8, 10, and 12, based on the examples in lower ranks.
However, these programs are irrelevant for verifying the correctness of the results from the article.
