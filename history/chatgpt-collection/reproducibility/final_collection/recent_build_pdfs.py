from pathlib import Path
import subprocess,json,concurrent.futures,shutil,hashlib,time,re
import fitz
R=Path(__file__).resolve().parents[2]
rows=json.loads((R/'catalogue/recent_entries.json').read_text())
def build(row):
 id=row['oeis_id']; src=R/row['manuscript_tex']; out=R/'reproducibility/final_collection/recent_pdf_build'/id;out.mkdir(parents=True,exist_ok=True)
 for repeat in range(2):
  proc=subprocess.run(['pdflatex','-halt-on-error','-interaction=nonstopmode',f'-output-directory={out}',str(src)],capture_output=True,text=True)
  (out/f'pdflatex-{repeat+1}.stdout.txt').write_text(proc.stdout+proc.stderr)
  if proc.returncode: return dict(id=id,exit_code=proc.returncode,error=(proc.stdout+proc.stderr)[-3500:])
 pdf=out/(id+'.pdf');target=R/row['manuscript_pdf'];shutil.copyfile(pdf,target)
 log=(out/(id+'.log')).read_text();issues=[s for s in log.splitlines() if re.search(r'(?:Overfull|Underfull|LaTeX Warning|Package .* Warning|Undefined)',s)]
 doc=fitz.open(target);bboxes=[]
 for n,page in enumerate(doc):
  for block in page.get_text('dict')['blocks']:
   if block.get('type')==0:
    for line in block['lines']:
     for span in line['spans']:
      x0,y0,x1,y1=span['bbox']
      if x0<0 or y0<0 or x1>page.rect.width or y1>page.rect.height:bboxes.append((n+1,span['text'],span['bbox']))
 rec=dict(id=id,exit_code=0,pages=len(doc),pdf_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),tex_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),warnings=issues,outside_page_text=bboxes)
 print(json.dumps(rec),flush=True);return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:res=list(ex.map(build,rows))
(R/'reproducibility/final_collection/recent_pdf_compile_report.json').write_text(json.dumps(res,indent=2)+'\n')
print('TOTAL PAGES',sum(r.get('pages',0) for r in res))
