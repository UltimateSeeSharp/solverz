import sys
sys.path.append(r"<user-site-packages>")
import fitz
doc = fitz.open(sys.argv[1])
with open(sys.argv[2], "w", encoding="utf-8") as out:
    for i, page in enumerate(doc):
        out.write(f"\n=== page {i+1} ===\n" + page.get_text())
print(len(doc), "pages")
