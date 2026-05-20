import csv
from pathlib import Path
import argparse

parser = argparse.ArgumentParser(description='Collect results from .result files')
parser.add_argument('result_dir', type=Path, help='Data directory containing result file')
args = parser.parse_args()

result_dir = args.result_dir

def split_res_csv(dir : Path, ewriter, ttwriter, tfwriter, fewriter):
  with open(dir / Path('results.csv'), 'r', newline='') as resfile:
    reader = csv.DictReader(resfile, fieldnames=['Thm_Name', 'Translatability_Stmt', 'Translatability_Sig', 'Reasons_Sig'], delimiter=';', quotechar='|', quoting=csv.QUOTE_MINIMAL)
    for row in reader:
      if not row['Thm_Name'] == 'Thm_Name':
        if row['Translatability_Stmt'] == 'Error':
          ewriter.writerow({'Thm_Name': row['Thm_Name'], 'Translatability_Stmt': row['Translatability_Stmt'], 'Translatability_Sig': row['Translatability_Sig'], 'Reasons_Sig': row['Reasons_Sig']})
        elif row['Translatability_Stmt'] == 'true':
          if row['Translatability_Sig'] == 'true':
            ttwriter.writerow({'Thm_Name': row['Thm_Name'], 'Translatability_Stmt': row['Translatability_Stmt'], 'Translatability_Sig': row['Translatability_Sig'], 'Reasons_Sig': row['Reasons_Sig']})
          else:
            tfwriter.writerow({'Thm_Name': row['Thm_Name'], 'Translatability_Stmt': row['Translatability_Stmt'], 'Translatability_Sig': row['Translatability_Sig'], 'Reasons_Sig': row['Reasons_Sig']})
        elif row['Translatability_Stmt'] == 'false':
          fewriter.writerow({'Thm_Name': row['Thm_Name'], 'Translatability_Stmt': row['Translatability_Stmt'], 'Translatability_Sig': row['Translatability_Sig'], 'Reasons_Sig': row['Reasons_Sig']})

with open(result_dir / Path('result_error.csv'),'w', newline='') as errfile:
  with open(result_dir / Path('result_true_true.csv'),'w', newline='') as truetruefile:
    with open(result_dir / Path('result_true_false.csv'),'w', newline='') as truefalsefile:
      with open(result_dir / Path('result_false.csv'),'w', newline='') as falsefile:
        errwriter = csv.DictWriter(errfile, fieldnames=['Thm_Name', 'Translatability_Stmt', 'Translatability_Sig', 'Reasons_Sig'], delimiter=';', quotechar='|', quoting=csv.QUOTE_MINIMAL)
        truetruewriter = csv.DictWriter(truetruefile, fieldnames=['Thm_Name', 'Translatability_Stmt', 'Translatability_Sig', 'Reasons_Sig'], delimiter=';', quotechar='|', quoting=csv.QUOTE_MINIMAL)
        truefalsewriter = csv.DictWriter(truefalsefile, fieldnames=['Thm_Name', 'Translatability_Stmt', 'Translatability_Sig', 'Reasons_Sig'], delimiter=';', quotechar='|', quoting=csv.QUOTE_MINIMAL)
        falsewriter = csv.DictWriter(falsefile, fieldnames=['Thm_Name', 'Translatability_Stmt', 'Translatability_Sig', 'Reasons_Sig'], delimiter=';', quotechar='|', quoting=csv.QUOTE_MINIMAL)
        errwriter.writeheader()
        truetruewriter.writeheader()
        truefalsewriter.writeheader()
        falsewriter.writeheader()
        split_res_csv(result_dir, errwriter, truetruewriter, truefalsewriter, falsewriter)
