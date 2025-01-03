
RUN_COUNT = 1
ELEMENT_COUNT = 5
LINEAR_COUNT = 30

import os

with open('poset_experiment/new_exp_template.py') as fp:
    rest = fp.read()

os.mkdir("poset_new_exp_batch")
os.system("cp poset_cover.py poset_new_exp_batch/")

i = RUN_COUNT
for ele in [ELEMENT_COUNT]:
    for lin in range(LINEAR_COUNT,LINEAR_COUNT+1,5):
        config = "batch = {batch};ele_count = {ele_count};lin_count = {lin_count}\n".format(batch=i, ele_count=ele, lin_count=lin)
        with open("poset_new_exp_batch/batch{}.py".format(i), 'w') as fp:
            fp.write(config+rest)
        i += 1

for j in range(1,i):
    os.system("python3 poset_new_exp_batch/batch{}.py &".format(j))
