from more_itertools import unique_everseen

with open('results_new/result_error.csv', 'r') as f, open('results_new/result_error_nd.csv', 'w') as out_file:
    out_file.writelines(unique_everseen(f))
with open('results_new/result_false.csv', 'r') as f, open('results_new/result_false_nd.csv', 'w') as out_file:
    out_file.writelines(unique_everseen(f))
with open('results_new/result_true_false.csv', 'r') as f, open('results_new/result_true_false_nd.csv', 'w') as out_file:
    out_file.writelines(unique_everseen(f))
with open('results_new/result_true_true.csv', 'r') as f, open('results_new/result_true_true_nd.csv', 'w') as out_file:
    out_file.writelines(unique_everseen(f))
with open('results_new/results.csv', 'r') as f, open('results_new/results_nd.csv', 'w') as out_file:
    out_file.writelines(unique_everseen(f))