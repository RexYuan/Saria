# SAT-Solving the Poset Cover Problem
The poset cover problem seeks a minimum set of partial orders whose linear extensions cover a given set of linear orders. Recognizing its NP-completeness, we devised a non-trivial reduction to the Boolean satisfiability problem using a technique we call swap graphs, which avoids the complexity explosion of the naive method. We also explore a special case solvable in polynomial time when the linear orders are linearizations of a single poset. By leveraging modern SAT solvers, we effectively solve instances with reasonable universe sizes. Experimental results using the Z3 theorem prover on randomly generated inputs demonstrate the effectiveness of our method.

## Setup
```
conda env create -f environment.yml
```

## Test
```
cd code
python3 poset_experiment/new_exp.py
```
Set the parameters in `poset_experiment/new_exp.py`. The default parameters are:
```
RUN_COUNT = 1
ELEMENT_COUNT = 5
LINEAR_COUNT = 30
```
The run status is in `new_status.txt`, the timeout result is in `new_timeout_log.txt`, and  the individual poset cover graph and swap graph are in `code/new_trials`.
