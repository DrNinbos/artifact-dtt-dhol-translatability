import csv
from pathlib import Path
import argparse

parser = argparse.ArgumentParser(description='Collect results from .result files')
parser.add_argument('result_dir', type=Path, help='Data directory containing result file')
args = parser.parse_args()

result_file = args.result_dir

def get_all_tf_reasons(resreader, reasonfile):
  reasons = []
  for row in resreader:
    if row['Translatability_Stmt'] == 'true' and row['Translatability_Sig'] == 'false':
      rsns = []
      for r in row['Reasons_Sig'].split(','):
        if not r.strip() in rsns:
          rsns.append(r.strip())
          reasons.append(r.strip())
  save = dict()
  for rsn in reasons:
    if not rsn in save:
      save[rsn] = 1
    else:
      save[rsn] += 1
  for k, v in save.items():
    reasonfile.write(k + '; ' + str(v) + '\n')

with open(result_file, 'r', newline='') as resfile, open(result_file.parent / f"reasons_{result_file.name}.txt", 'a') as reasonfile:
  reader = csv.DictReader(resfile, fieldnames=['Thm_Name', 'Translatability_Stmt', 'Translatability_Sig', 'Reasons_Sig'], delimiter=';', quotechar='|', quoting=csv.QUOTE_MINIMAL)
  get_all_tf_reasons(reader, reasonfile)