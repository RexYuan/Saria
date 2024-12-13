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
