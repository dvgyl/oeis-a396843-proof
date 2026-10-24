from pathlib import Path
import json,fitz
from PIL import Image,ImageDraw
R=Path(__file__).resolve().parents[2]
rows=json.loads((R/'catalogue/recent_entries.json').read_text())
out=R/'reproducibility/final_collection/recent_pdf_renders';out.mkdir(exist_ok=True)
for row in rows:
 id=row['oeis_id'];doc=fitz.open(R/row['manuscript_pdf']);panels=[]
 for n,page in enumerate(doc):
  p=page.get_pixmap(matrix=fitz.Matrix(1,1),alpha=False);im=Image.frombytes('RGB',[p.width,p.height],p.samples)
  panel=Image.new('RGB',(p.width,p.height+24),'#eeeeee');panel.paste(im,(0,24));ImageDraw.Draw(panel).text((10,6),f'{id} / page {n+1}',fill='black');panels.append(panel)
  im.save(out/f'{id}_page_{n+1:02}.png')
 w=max(p.width for p in panels);h=max(p.height for p in panels);sheet=Image.new('RGB',(w*2,h*((len(panels)+1)//2)),'#b5b5b5')
 for n,panel in enumerate(panels):sheet.paste(panel,((n%2)*w,(n//2)*h))
 sheet.save(out/f'{id}_contact.png')
print(out)
