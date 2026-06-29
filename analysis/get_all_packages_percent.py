import csv
from pathlib import Path
import argparse

parser = argparse.ArgumentParser(description='Collect results from .result files')
parser.add_argument('data_dir', type=Path, help='Data directory containing result file')
parser.add_argument('mathlib_dir', type=Path, help='Output directory for parquet file')
parser.add_argument('module_level', type=int, help='Number of Submodulelevels to be listed')
args = parser.parse_args()

data_dir = args.data_dir
mathlib_dir = args.mathlib_dir
lvls = args.module_level

def get_all_pkg_prcnt_top(dir : Path):
  truect = 0
  ct = 0
  pkg_prct = []
  sub_pkgs = []
  for p in dir.iterdir():
    if p.is_dir():
      sub_res = get_all_pkg_prcnt(p)
      truect += sub_res[0][1]
      ct += sub_res[0][2]
      sub_pkgs.extend(get_all_pkg_prcnt(p))
    else:
      if p.name.endswith('.csv'):
        with open(p,'r',newline='') as resfile:
          reader = csv.DictReader(resfile, fieldnames=['Thm_Name', 'Translatability_Stmt', 'Translatability_Sig', 'Reasons_Sig'], delimiter=';', quotechar='|', quoting=csv.QUOTE_MINIMAL)
          for row in reader:
            if not row['Translatability_Stmt'] == 'Translatability_Stmt':
              ct += 1
              if row['Translatability_Stmt'] == 'true' and row['Translatability_Sig'] == 'true':
                truect += 1
  pkg_prct.append((dir.relative_to(mathlib_dir), truect, ct))
  pkg_prct.extend(sub_pkgs)
  return pkg_prct

def get_all_pkg_prcnt(dir : Path, lvl = 0):
  truect = 0
  ct = 0
  pkg_prct = []
  sub_pkgs = []
  for p in dir.iterdir():
    if p.is_dir():
      sub_res = get_all_pkg_prcnt(p, lvl - 1)
      truect += sub_res[0][1]
      ct += sub_res[0][2]
      sub_pkgs.extend(sub_res)
    else:
      if p.name.endswith('.csv'):
        with open(p,'r',newline='') as resfile:
          reader = csv.DictReader(resfile, fieldnames=['Thm_Name', 'Translatability_Stmt', 'Translatability_Sig', 'Reasons_Sig'], delimiter=';', quotechar='|', quoting=csv.QUOTE_MINIMAL)
          for row in reader:
            if not row['Translatability_Stmt'] == 'Translatability_Stmt':
              ct += 1
              if row['Translatability_Stmt'] == 'true' and row['Translatability_Sig'] == 'true':
                truect += 1
  pkg_prct.append((dir.relative_to(mathlib_dir), truect, ct))
  if lvl > 0:
    pkg_prct.extend(sub_pkgs)
  return pkg_prct

all_pkg_prcnt = get_all_pkg_prcnt(data_dir, lvls)
with open(data_dir / '..' / 'result_percentages.csv', 'w', newline='') as resultfile:
  writer = csv.DictWriter(resultfile, fieldnames=['Pkg_name', 'Total_Thms', 'Translatability_%'], delimiter=';', quotechar='|', quoting=csv.QUOTE_MINIMAL)
  writer.writeheader()
  for p, tr, to in all_pkg_prcnt:
    if not to == 0:
      writer.writerow({'Pkg_name': p, 'Total_Thms': to, 'Translatability_%': tr / to})
