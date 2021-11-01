from collections import defaultdict
import matplotlib.pyplot as plt
import numpy as np
import os
import math

def read_file_contents(file_name, filter_times_dict, times_dict):
    with open(file_name) as file:
        lines = file.readlines()
        for i in range(len(lines) -1):  
            if "genAbstractState pred count" in lines[i].split('\t')[-1] and lines[i+1].split('\t')[-1].startswith("genAbstractState pred time"):
                predicate_count = int(lines[i].split()[-1])
                predicate_time = float(lines[i+1].split()[-1])
                times_dict[predicate_count].append(predicate_time)
            if "filter" in lines[i].split('\t')[-1]:
                filter_time_ms = int(lines[i].split()[-1])
                
                benchmark_id = int(file_name.split('.smt2')[0].split('/')[-1].split('_')[-1])
                filter_times_dict[benchmark_id] = filter_time_ms


def read_folder(folder_name):
    times = defaultdict(lambda: [].copy())
    filter_times_dict = defaultdict(lambda: 0)

    for root, dirs, files in os.walk(folder_name):
        for file in files:
            #print(os.path.join(root, file))
            read_file_contents(os.path.join(root, file), filter_times_dict, times)

    print(list(map(lambda x: np.std(np.array(times[x])), times)))

    times_std = list(map(lambda x: np.std(np.array(times[x])), times))
    times_mean = list(map(lambda x: np.mean(np.array(times[x])), times))

    times_x = list(map(lambda x: x, times))
    times_x_count = list(map(lambda x: len(times[x]), times))
       
    return (times_x, times_x_count, times_mean, times_std, filter_times_dict)

def compute_difference(par_dict, seq_dict, slice_begin=0, slice_end=-1, min_time=0):
    difference_x = []
    difference_y = []
    for key in sorted(par_dict.keys())[slice_begin:slice_end]:
        if key in par_dict and par_dict[key] != 0 and seq_dict[key] != 0 and par_dict[key] > min_time:
            difference_x.append(key)
            difference_y.append(seq_dict[key] / par_dict[key])
    return difference_x, difference_y

seq_times_x, seq_times_x_count, seq_times_mean, seq_times_std, seq_filter_times_dict = read_folder("Debug Solver___sequential")

seq_abst_times_x, seq_abst_times_x_count, seq_abst_times_mean, seq_abst_times_std, seq_abst_filter_times_dict = read_folder("Debug Solver___sequential_abstract_off")

seq_nohash_times_x, seq_nohash_times_x_count, seq_nohash_times_mean, seq_nohash_times_std, seq_nohash_filter_times_dict = read_folder("Debug Solver___sequential_hashing_off")

par_times_x, par_times_x_count, par_times_mean, par_times_std, par_filter_times_dict = read_folder("Debug Solver___parallel_implications")
par2_times_x, par2_times_x_count, par2_times_mean, par2_times_std, par2_filter_times_dict = read_folder("Debug Solver___parallel_implications_min2")

# compare filter times

width = 0.2
min_time_ms = 0 
slice_begin = 0
slice_end = -1

difference_x, difference_y = compute_difference(par_filter_times_dict, seq_filter_times_dict, slice_begin, slice_end, min_time_ms)         
plt.bar(difference_x, difference_y, width)

difference_x_abst, difference_y_abst = compute_difference(par_filter_times_dict, seq_abst_filter_times_dict, slice_begin, slice_end, min_time_ms)         
plt.bar(np.array(difference_x_abst) + width, difference_y_abst, width)

difference_x_nohash, difference_y_nohash = compute_difference(par_filter_times_dict, seq_nohash_filter_times_dict, slice_begin, slice_end, min_time_ms)         
plt.bar(np.array(difference_x_nohash) + (width * 2), difference_y_nohash, width)

difference_x_par2, difference_y_par2 = compute_difference(par_filter_times_dict, par2_filter_times_dict, slice_begin, slice_end, min_time_ms)         
plt.bar(np.array(difference_x_par2) + (width * 3), difference_y_par2, width)

plt.title("Speedup")
plt.legend(['vs. seq', 'vs. seq_abstract:off', 'vs. seq_hashing:off', 'vs. par_min2'])

print(f'average speedup (seq): {np.mean(difference_y)} min: {np.min(difference_y)} max: {np.max(difference_y)}')
print(f'average speedup (seq_abst): {np.mean(difference_y_abst)} min: {np.min(difference_y_abst)} max: {np.max(difference_y_abst)}')
print(f'average speedup (seq_hash): {np.mean(difference_y_nohash)} min: {np.min(difference_y_nohash)} max: {np.max(difference_y_nohash)}')
print(f'average speedup (par_min2): {np.mean(difference_y_par2)} min: {np.min(difference_y_par2)} max: {np.max(difference_y_par2)}')
plt.show()





