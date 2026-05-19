#!/usr/bin/env python
import csv
from pathlib import Path
import argparse

parser = argparse.ArgumentParser(description='Collect results from .result files')
parser.add_argument('data_dir', type=Path, help='Data directory containing result files')
parser.add_argument('output_dir', type=Path, help='Output directory for parquet file')
args = parser.parse_args()

data_dir = args.data_dir
output_dir = args.output_dir

def results_as_csvs(dir : Path):
  for p in dir.iterdir():
    if p.is_dir():
      results_as_csvs(p)
    else:
      if p.name.endswith('.result'):
        with open(dir / Path(p.name[:len(p.name)-7] + '.csv'), 'w', newline='') as csvfile:
          writer = csv.DictWriter(csvfile, fieldnames=['Thm_Name', 'Translatability_Stmt', 'Translatability_Sig', 'Reasons_Sig'], delimiter=';', quotechar='|', quoting=csv.QUOTE_MINIMAL)
          writer.writeheader()
          with open(p, "r") as fp:
            for line in fp:
              data = line.split()
              if len(data) == 3:
                writer.writerow({'Thm_Name': data[0], 'Translatability_Stmt': 'Error'})
              if len(data) > 3:
                writer.writerow({'Thm_Name': data[0], 'Translatability_Stmt': data[2].strip(','), 'Translatability_Sig': data[5], 'Reasons_Sig': (' '.join(data[6:])).strip('#[]')})

def merge_all_csvs(dir : Path, writer):
  for p in dir.iterdir():
    if p.is_dir():
      merge_all_csvs(p, writer)
    else:
      if p.name.endswith('.csv'):
        print(p)
        with open(p, 'r', newline='') as csvfile:
          reader = csv.DictReader(csvfile, fieldnames=['Thm_Name', 'Translatability_Stmt', 'Translatability_Sig', 'Reasons_Sig'], delimiter=';', quotechar='|', quoting=csv.QUOTE_MINIMAL)
          for row in reader:
            if not row['Thm_Name'] == 'Thm_Name':
              writer.writerow({'Thm_Name': row['Thm_Name'], 'Translatability_Stmt': row['Translatability_Stmt'], 'Translatability_Sig': row['Translatability_Sig'], 'Reasons_Sig': row['Reasons_Sig']})

results_as_csvs(data_dir)
with open(data_dir / Path('results.csv'), 'w', newline='') as resultfile:
  writer = csv.DictWriter(resultfile, fieldnames=['Thm_Name', 'Translatability_Stmt', 'Translatability_Sig', 'Reasons_Sig'], delimiter=';', quotechar='|', quoting=csv.QUOTE_MINIMAL)
  writer.writeheader()
  merge_all_csvs(data_dir, writer)